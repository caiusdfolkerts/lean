module
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import sunlet.cyclic_sparse_witness
public import sunlet.verified_generic_open

@[expose] public section
set_option Elab.async false

#check "SUNLET_VERIFIEDCYCLICFIELD_IMPORTS_READY"

section Stage_RationalSubfamily


/-! Exact field embeddings induced by injections of independent parameter
indices, and algebraicity after the image of the smaller base field is
contained in the larger base field. -/

noncomputable section

namespace Sunlet.RationalSubfamily

variable {k I J : Type*} [Field k]

abbrev Rational (I : Type*) := FractionRing (MvPolynomial I k)

def polynomialMap (e : J → I) : MvPolynomial J k →ₐ[k] Rational (k := k) I :=
  (IsScalarTower.toAlgHom k (MvPolynomial I k) (Rational (k := k) I)).comp
    (MvPolynomial.rename e)

theorem polynomialMap_injective (e : J → I) (he : Function.Injective e) :
    Function.Injective (polynomialMap (k := k) e) :=
  (IsFractionRing.injective (MvPolynomial I k) (Rational (k := k) I)).comp
    (MvPolynomial.rename_injective _ he)

def embedding (e : J → I) (he : Function.Injective e) :
    Rational (k := k) J →ₐ[k] Rational (k := k) I :=
  IsFractionRing.liftAlgHom (polynomialMap_injective (k := k) e he)

@[simp] theorem embedding_variable (e : J → I) (he : Function.Injective e) (j : J) :
    embedding (k := k) e he
      (algebraMap (MvPolynomial J k) (Rational (k := k) J) (MvPolynomial.X j)) =
      algebraMap (MvPolynomial I k) (Rational (k := k) I) (MvPolynomial.X (e j)) := by
  simp [embedding, polynomialMap]

section Algebraic

variable {E E' : Type*} [Field E] [Field E'] [Algebra k E] [Algebra k E']
  (S : IntermediateField k E) (F : IntermediateField k E')
  (φ : E →ₐ[k] E') (hφ : ∀ s : S, φ s.val ∈ F)

def baseEmbedding : S →ₐ[k] F where
  toFun s := ⟨φ s.val, hφ s⟩
  map_zero' := Subtype.ext (map_zero φ)
  map_one' := Subtype.ext (map_one φ)
  map_add' _ _ := Subtype.ext (map_add φ _ _)
  map_mul' _ _ := Subtype.ext (map_mul φ _ _)
  commutes' c := Subtype.ext (φ.commutes c)

include hφ in
theorem image_isAlgebraic [Algebra.IsAlgebraic S E] (x : E) :
    IsAlgebraic F (φ x) := by
  let ρ : S →ₐ[k] F := baseEmbedding S F φ hφ
  letI : Algebra S F := ρ.toRingHom.toAlgebra
  letI : Algebra S E' := (φ.comp S.val).toRingHom.toAlgebra
  letI : IsScalarTower S F E' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let ψ : E →ₐ[S] E' :=
    { __ := φ.toRingHom, commutes' := fun _ => rfl }
  exact ((Algebra.IsAlgebraic.isAlgebraic (R := S) x).algHom ψ).tower_top F

end Algebraic
end Sunlet.RationalSubfamily
end
end Stage_RationalSubfamily
#check "SUNLET_VERIFIEDCYCLICFIELD_RationalSubfamily_DONE"

section Stage_CyclicTorusRecovery


/-! A single full color, namely translation by one, determines the
one-component torus ambiguity as an actual character of the cyclic group. -/

noncomputable section

namespace Sunlet.CyclicTorusRecovery

variable {m : ℕ} [NeZero m]

section Group

variable {M : Type*} [CommGroup M]

theorem additive_of_successor (χ : ZMod m → M) (h0 : χ 0 = 1)
    (hs : ∀ b, χ (1 + b) = χ 1 * χ b) :
    ∀ a b, χ (a + b) = χ a * χ b := by
  have hn : ∀ n : ℕ, ∀ b : ZMod m,
      χ ((n : ZMod m) + b) = χ (n : ZMod m) * χ b := by
    intro n
    induction n with
    | zero => intro b; simp [h0]
    | succ n ih =>
        intro b
        rw [Nat.cast_succ, add_comm (n : ZMod m) 1, add_assoc, hs, ih, hs, mul_assoc]
  intro a b
  simpa only [ZMod.natCast_zmod_val] using hn a.val b

/-- The equality of the full color-one rows is sufficient; no equation
from an unobserved color is used here. -/
theorem quotient_additive (u v : M) (h g : ZMod m → M)
    (h0 : h 0 = 1) (g0 : g 0 = 1)
    (heq : ∀ b, u * h b / h (1 + b) = v * g b / g (1 + b)) :
    ∀ a b, g (a + b) / h (a + b) = (g a / h a) * (g b / h b) := by
  let χ : ZMod m → M := fun b => g b / h b
  have htorus : ∀ b, g b = h b * χ b := by intro b; simp [χ, mul_comm]
  have hcoeff : v = u * χ 1 := by
    have hh := (heq 0).symm
    simp only [h0, g0, mul_one, add_zero] at hh
    calc
      v = (v / g 1) * g 1 := by simp
      _ = (u / h 1) * g 1 := congrArg (fun z : M => z * g 1) hh
      _ = u * χ 1 := by simp only [χ, div_eq_mul_inv]; ac_rfl
  apply additive_of_successor χ (by simp [χ, h0, g0])
  intro b
  have he : v * g b / g (1 + b) =
      (u * h b / h (1 + b)) * (χ 1 * χ b / χ (1 + b)) := by
    rw [hcoeff, htorus b, htorus (1 + b), mul_mul_mul_comm, mul_div_mul_comm]
  have hh : (u * h b / h (1 + b)) * (χ 1 * χ b / χ (1 + b)) =
      (u * h b / h (1 + b)) * 1 := by
    rw [← he, ← heq b, mul_one]
  exact (div_eq_one.mp (mul_left_cancel hh)).symm

end Group

section Field

variable {K : Type*} [Field K]

/-- A direct scalar version used for embeddings of the actual parameter
field, with nonvanishing proved for the coefficient being inverted. -/
theorem quotient_character_of_row (u v : K) (hu : u ≠ 0) (hv : v ≠ 0)
    (h g : ZMod m → Kˣ) (h0 : h 0 = 1) (g0 : g 0 = 1)
    (heq : ∀ b, u * ((h b).val / (h (1 + b)).val) =
      v * ((g b).val / (g (1 + b)).val)) :
    ∀ a b, g (a + b) / h (a + b) = (g a / h a) * (g b / h b) := by
  apply quotient_additive (Units.mk0 u hu) (Units.mk0 v hv) h g h0 g0
  intro b
  apply Units.ext
  simpa only [Units.val_div_eq_div_val, Units.val_mul, Units.val_mk0, mul_div_assoc] using heq b

/-- Two observations recover the affine coefficients whenever the
literal two-by-two determinant is nonzero. -/
theorem two_row_coefficients_unique
    (A B C D U V U' V' : K) (hdet : A * D - B * C ≠ 0)
    (h0 : A * U + B * V = A * U' + B * V')
    (h1 : C * U + D * V = C * U' + D * V') : U = U' ∧ V = V' := by
  have hu : (A * D - B * C) * (U - U') = 0 := by
    linear_combination D * h0 - B * h1
  have hv : (A * D - B * C) * (V - V') = 0 := by
    linear_combination A * h1 - C * h0
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hu).resolve_left hdet),
    sub_eq_zero.mp ((mul_eq_zero.mp hv).resolve_left hdet)⟩

theorem coefficient_left_formula
    (A B C D U V y z : K) (hdet : A * D - B * C ≠ 0)
    (hy : A * U + B * V = y) (hz : C * U + D * V = z) :
    U = (D * y - B * z) / (A * D - B * C) := by
  apply (eq_div_iff hdet).mpr
  linear_combination D * hy - B * hz

theorem coefficient_right_formula
    (A B C D U V y z : K) (hdet : A * D - B * C ≠ 0)
    (hy : A * U + B * V = y) (hz : C * U + D * V = z) :
    V = (A * z - C * y) / (A * D - B * C) := by
  apply (eq_div_iff hdet).mpr
  linear_combination A * hz - C * hy

end Field

end Sunlet.CyclicTorusRecovery
end
end Stage_CyclicTorusRecovery
#check "SUNLET_VERIFIEDCYCLICFIELD_CyclicTorusRecovery_DONE"

section Stage_CyclicSelectedField


/-! The actual five-color rational subfamily inside the full cyclic
parameter field, together with the two observations retained in every
remaining row. -/

noncomputable section

namespace Sunlet.CyclicSelectedField

open ToricPairAlgebra

variable {k : Type*} [Field k] [CharZero k] (m : ℕ) [NeZero m]

abbrev Color := {a : ZMod m // a ≠ 0}
def permutation (a : Color m) : Equiv.Perm (ZMod m) := Equiv.addLeft a.val
abbrev FullField := FunctionField (k := k) (ι := Color m) (0 : ZMod m)
abbrev SmallField := FunctionField (k := k) (ι := Fin 5) (0 : ZMod m)

def colorEmbedding (hm : 6 ≤ m) : Fin 5 → Color m :=
  fun a => ⟨CyclicSparseWitness.shift m a,CyclicSparseWitness.shift_ne_zero m hm a⟩

theorem colorEmbedding_injective (hm : 6 ≤ m) : Function.Injective (colorEmbedding m hm) :=
  fun _ _ h => CyclicSparseWitness.shift_injective m hm (congrArg Subtype.val h)

def indexEmbedding (hm : 6 ≤ m) : Index (ι := Fin 5) (0 : ZMod m) →
    Index (ι := Color m) (0 : ZMod m) :=
  fun j => (j.1,Sum.map (colorEmbedding m hm) id j.2)

theorem indexEmbedding_injective (hm : 6 ≤ m) : Function.Injective (indexEmbedding m hm) := by
  rintro ⟨b,i⟩ ⟨c,j⟩ h
  have hb : b=c := congrArg Prod.fst h
  subst c
  congr 1
  have hi := congrArg Prod.snd h
  cases i <;> cases j <;> simp only [indexEmbedding,Sum.map_inl,Sum.map_inr,
    Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl] at hi ⊢
  · exact colorEmbedding_injective m hm hi
  · exact hi

def inclusion (hm : 6 ≤ m) : SmallField (k := k) m →ₐ[k] FullField (k := k) m :=
  RationalSubfamily.embedding (indexEmbedding m hm) (indexEmbedding_injective m hm)

@[simp] theorem inclusion_variable (hm : 6 ≤ m) (j : Index (ι := Fin 5) (0 : ZMod m)) :
    inclusion (k := k) m hm (genericVariable 0 j) =
      genericVariable 0 (indexEmbedding m hm j) :=
  RationalSubfamily.embedding_variable _ _ j

@[simp] theorem inclusion_torus (hm : 6 ≤ m) (b : Bool) (x : ZMod m) :
    inclusion (k := k) m hm (genericTorus (k := k) (ι := Fin 5) 0 b x).val =
      (genericTorus (k := k) (ι := Color m) 0 b x).val := by
  by_cases hx : x=0
  · subst x; simp
  · simp only [genericTorus,dif_neg hx,Units.val_mk0,inclusion_variable,indexEmbedding,
      Sum.map_inr,id_eq]

@[simp] theorem inclusion_point (hm : 6 ≤ m) (b : Bool) (a : Fin 5) (x : ZMod m) :
    inclusion (k := k) m hm (genericPoint 0 (CyclicSparseWitness.permutation m) b (a,x)) =
      genericPoint 0 (permutation m) b (colorEmbedding m hm a,x) := by
  simp only [ToricPairAlgebra.genericPoint,ToricDifferential.coordinate,ToricDifferential.ratio,
    map_mul,map_div₀,genericCoefficient,inclusion_variable,inclusion_torus,indexEmbedding,
    Sum.map_inl]
  rfl

@[simp] theorem inclusion_coordinate (hm : 6 ≤ m) (a : Fin 5) (x : ZMod m) :
    inclusion (k := k) m hm (genericCoordinates 0 (CyclicSparseWitness.permutation m) (a,x)) =
      genericCoordinates 0 (permutation m) (colorEmbedding m hm a,x) := by
  change inclusion (k := k) m hm
      (genericPoint 0 (CyclicSparseWitness.permutation m) false (a,x) +
        genericPoint 0 (CyclicSparseWitness.permutation m) true (a,x)) =
    genericPoint 0 (permutation m) false (colorEmbedding m hm a,x) +
      genericPoint 0 (permutation m) true (colorEmbedding m hm a,x)
  rw [map_add,inclusion_point,inclusion_point]

def Retained (hm : 6 ≤ m) (ax : Color m × ZMod m) : Prop :=
  ax.1 ∈ Set.range (colorEmbedding m hm) ∨ ax.2=0 ∨ ax.2= -ax.1.val

abbrev Observed (hm : 6 ≤ m) := {ax : Color m × ZMod m // Retained m hm ax}

def observedCoordinates (hm : 6 ≤ m) : Observed m hm → FullField (k := k) m :=
  fun ax => genericCoordinates 0 (permutation m) ax.val

abbrev ObservedField (hm : 6 ≤ m) := IntermediateField.adjoin k
  (Set.range (observedCoordinates (k := k) m hm))

abbrev SmallImage := JacobianFinite.generatedField
  (genericCoordinates (k := k) (0 : ZMod m) (CyclicSparseWitness.permutation m))

theorem observed_mem (hm : 6 ≤ m) (ax : Color m × ZMod m) (hx : Retained m hm ax) :
    genericCoordinates (k := k) 0 (permutation m) ax ∈ ObservedField (k := k) m hm :=
  IntermediateField.subset_adjoin k _ ⟨⟨ax,hx⟩,rfl⟩

theorem small_image_mem (hm : 6 ≤ m) (x : SmallImage (k := k) m) :
    inclusion (k := k) m hm x.val ∈ ObservedField (k := k) m hm := by
  refine IntermediateField.adjoin_induction k
    (motive := fun x _ => inclusion (k := k) m hm x ∈ ObservedField (k := k) m hm)
    ?_ ?_ ?_ ?_ ?_ x.property
  · rintro _ ⟨⟨a,b⟩,rfl⟩
    rw [inclusion_coordinate]
    exact observed_mem m hm _ (Or.inl ⟨a,rfl⟩)
  · intro c
    rw [AlgHom.commutes]
    exact (ObservedField (k := k) m hm).algebraMap_mem c
  · intro a b _ _ ha hb
    simpa only [map_add] using (ObservedField (k := k) m hm).add_mem ha hb
  · intro a _ ha
    simpa only [map_inv₀] using (ObservedField (k := k) m hm).inv_mem ha
  · intro a b _ _ ha hb
    simpa only [map_mul] using (ObservedField (k := k) m hm).mul_mem ha hb

theorem small_finite (hm : 6 ≤ m) : Module.Finite (SmallImage (k := k) m) (SmallField (k := k) m) := by
  let W := CyclicSparseWitness.witness (k := k) m hm
  exact (generic_finite_separable 0 (CyclicSparseWitness.permutation m)
    (W.A : Set (Fin 5)) (W.B : Set (Fin 5)) W.disjoint
    (fun a => CyclicSparseWitness.derangement m hm a 0)
    W.Atwo W.Btwo W.Atrans W.Btrans).1

theorem torus_isAlgebraic (hm : 6 ≤ m) (b : Bool) (x : ZMod m) :
    IsAlgebraic (ObservedField (k := k) m hm)
      (genericTorus (k := k) (ι := Color m) 0 b x).val := by
  letI := small_finite (k := k) m hm
  have hh := RationalSubfamily.image_isAlgebraic (SmallImage (k := k) m)
    (ObservedField (k := k) m hm) (inclusion (k := k) m hm) (small_image_mem m hm)
    (genericTorus (k := k) (ι := Fin 5) 0 b x).val
  simpa only [inclusion_torus] using hh

/-- The actual determinant used to recover the two coefficients in every
unobserved row. No generic-nonzero hypothesis is assumed. -/
def rowDeterminant (a : Color m) : FullField (k := k) m :=
  (genericTorus (k := k) (ι := Color m) 0 true (-a.val)).val /
      (genericTorus (k := k) (ι := Color m) 0 false a.val).val -
    (genericTorus (k := k) (ι := Color m) 0 false (-a.val)).val /
      (genericTorus (k := k) (ι := Color m) 0 true a.val).val

theorem rowDeterminant_ne_zero (a : Color m) : rowDeterminant (k := k) m a ≠ 0 := by
  intro he
  have ha := a.property
  have hna : -a.val ≠ 0 := neg_ne_zero.mpr ha
  let pos : {x : ZMod m // x ≠ 0} := ⟨a.val, ha⟩
  let neg : {x : ZMod m // x ≠ 0} := ⟨-a.val, hna⟩
  have hh : genericVariable (k := k) (ι := Color m) 0 (true, .inr neg) /
        genericVariable (k := k) (ι := Color m) 0 (false, .inr pos) =
      genericVariable (k := k) (ι := Color m) 0 (false, .inr neg) /
        genericVariable (k := k) (ι := Color m) 0 (true, .inr pos) := by
    apply sub_eq_zero.mp
    simpa only [rowDeterminant, genericTorus, dif_neg ha, dif_neg hna,
      Units.val_mk0, pos, neg] using he
  have hz := (div_eq_div_iff
    (genericVariable_ne_zero (k := k) (ι := Color m) 0 (false, .inr pos))
    (genericVariable_ne_zero (k := k) (ι := Color m) 0 (true, .inr pos))).mp hh
  let P : PolynomialRing (k := k) (ι := Color m) (0 : ZMod m) :=
    MvPolynomial.X (true, Sum.inr neg) * MvPolynomial.X (true, Sum.inr pos) -
      MvPolynomial.X (false, Sum.inr neg) * MvPolynomial.X (false, Sum.inr pos)
  have hP : algebraMap (PolynomialRing (k := k) (ι := Color m) (0 : ZMod m))
      (FullField (k := k) m) P = 0 := by
    simpa only [P, map_sub, map_mul, genericVariable] using sub_eq_zero.mpr hz
  have hp0 : P = 0 := (IsFractionRing.injective
    (PolynomialRing (k := k) (ι := Color m) (0 : ZMod m))
    (FullField (k := k) m)) (by simpa only [map_zero] using hP)
  have hspec := congrArg (MvPolynomial.eval
    (fun j : Index (ι := Color m) (0 : ZMod m) => if j.1 then (2 : k) else 1)) hp0
  norm_num [P] at hspec

@[simp] theorem coordinate_zero (a : Color m) :
    genericCoordinates (k := k) 0 (permutation m) (a,0) =
      genericCoefficient 0 false a / (genericTorus (k := k) (ι := Color m) 0 false a.val).val +
      genericCoefficient 0 true a / (genericTorus (k := k) (ι := Color m) 0 true a.val).val := by
  simp [genericCoordinates,ToricDifferential.coordinate,ToricDifferential.ratio,
    permutation, div_eq_mul_inv]

@[simp] theorem coordinate_neg (a : Color m) :
    genericCoordinates (k := k) 0 (permutation m) (a,-a.val) =
      genericCoefficient 0 false a * (genericTorus (k := k) (ι := Color m) 0 false (-a.val)).val +
      genericCoefficient 0 true a * (genericTorus (k := k) (ι := Color m) 0 true (-a.val)).val := by
  simp [genericCoordinates,ToricDifferential.coordinate,ToricDifferential.ratio,
    permutation]

theorem coefficient_isAlgebraic (hm : 6 ≤ m) (b : Bool) (a : Color m) :
    IsAlgebraic (ObservedField (k := k) m hm)
      (genericCoefficient (k := k) (ι := Color m) (0 : ZMod m) b a) := by
  let F := ObservedField (k := k) m hm
  let C := algebraicClosure F (FullField (k := k) m)
  have ht (b : Bool) (x : ZMod m) :
      (genericTorus (k := k) (ι := Color m) 0 b x).val ∈ C :=
    mem_algebraicClosure_iff.mpr (torus_isAlgebraic m hm b x)
  have hq (x : ZMod m) (hx : x=0 ∨ x= -a.val) :
      genericCoordinates (k := k) 0 (permutation m) (a,x) ∈ C := by
    let q : F := ⟨genericCoordinates 0 (permutation m) (a,x),
      observed_mem m hm _ (Or.inr hx)⟩
    exact C.algebraMap_mem q
  let A : FullField (k := k) m := ((genericTorus (k := k) (ι := Color m) 0 false a.val).val)⁻¹
  let B : FullField (k := k) m := ((genericTorus (k := k) (ι := Color m) 0 true a.val).val)⁻¹
  let C' : FullField (k := k) m := (genericTorus (k := k) (ι := Color m) 0 false (-a.val)).val
  let D : FullField (k := k) m := (genericTorus (k := k) (ι := Color m) 0 true (-a.val)).val
  have hd : A*D-B*C' ≠ 0 := by
    simpa only [A,B,C',D,rowDeterminant,div_eq_mul_inv,mul_comm] using rowDeterminant_ne_zero (k := k) m a
  have h0 : A*genericCoefficient 0 false a+B*genericCoefficient 0 true a =
      genericCoordinates (k := k) 0 (permutation m) (a,0) := by
    rw [coordinate_zero]
    simp only [A,B,div_eq_mul_inv,mul_comm]
  have h1 : C'*genericCoefficient 0 false a+D*genericCoefficient 0 true a =
      genericCoordinates (k := k) 0 (permutation m) (a,-a.val) := by
    rw [coordinate_neg]
    simp only [C',D,mul_comm]
  have hA : A ∈ C := C.inv_mem (ht false a.val)
  have hB : B ∈ C := C.inv_mem (ht true a.val)
  have hC : C' ∈ C := ht false (-a.val)
  have hD : D ∈ C := ht true (-a.val)
  apply mem_algebraicClosure_iff.mp
  change genericCoefficient (k := k) (ι := Color m) (0 : ZMod m) b a ∈ C
  cases b
  · rw [CyclicTorusRecovery.coefficient_left_formula A B C' D _ _ _ _ hd h0 h1]
    exact C.div_mem (C.sub_mem (C.mul_mem hD (hq 0 (Or.inl rfl)))
      (C.mul_mem hB (hq (-a.val) (Or.inr rfl))))
      (C.sub_mem (C.mul_mem hA hD) (C.mul_mem hB hC))
  · rw [CyclicTorusRecovery.coefficient_right_formula A B C' D _ _ _ _ hd h0 h1]
    exact C.div_mem (C.sub_mem (C.mul_mem hA (hq (-a.val) (Or.inr rfl)))
      (C.mul_mem hC (hq 0 (Or.inl rfl))))
      (C.sub_mem (C.mul_mem hA hD) (C.mul_mem hB hC))

/-- Every full parameter is algebraic over the actual retained-coordinate
field. Missing coefficients are solved from the two retained observations. -/
theorem full_isAlgebraic (hm : 6 ≤ m) :
    Algebra.IsAlgebraic (ObservedField (k := k) m hm) (FullField (k := k) m) := by
  let F := ObservedField (k := k) m hm
  let C := algebraicClosure F (FullField (k := k) m)
  have hv (j : Index (ι := Color m) (0 : ZMod m)) :
      genericVariable (k := k) 0 j ∈ C := by
    rcases j with ⟨b,a | x⟩
    · exact mem_algebraicClosure_iff.mpr (coefficient_isAlgebraic m hm b a)
    · have hh := mem_algebraicClosure_iff.mpr (torus_isAlgebraic (k := k) m hm b x.val)
      simpa only [genericTorus,dif_neg x.property,Units.val_mk0] using hh
  have hp (p : PolynomialRing (k := k) (ι := Color m) (0 : ZMod m)) :
      algebraMap (PolynomialRing (k := k) (ι := Color m) (0 : ZMod m))
        (FullField (k := k) m) p ∈ C := by
    induction p using MvPolynomial.induction_on with
    | C c =>
      change algebraMap k (FullField (k := k) m) c ∈ C
      rw [IsScalarTower.algebraMap_apply k F (FullField (k := k) m)]
      exact C.algebraMap_mem _
    | add p q hp hq => simpa only [map_add] using C.add_mem hp hq
    | mul_X p j hp => simpa only [map_mul, genericVariable] using C.mul_mem hp (hv j)
  constructor
  intro x
  apply mem_algebraicClosure_iff.mp
  obtain ⟨p,q,_,rfl⟩ := IsFractionRing.div_surjective
    (PolynomialRing (k := k) (ι := Color m) (0 : ZMod m)) x
  exact C.div_mem (hp p) (hp q)

end Sunlet.CyclicSelectedField
end
end Stage_CyclicSelectedField
#check "SUNLET_VERIFIEDCYCLICFIELD_CyclicSelectedField_DONE"

section Stage_CyclicCompleteRecovery


/-! Recovering every missing cyclic row from the retained row of shift
one and the two retained entries. The character quotient is derived from
that row; it is not assumed. -/

noncomputable section

namespace Sunlet.CyclicCompleteRecovery

variable {K : Type*} [Field K] (m : ℕ) [NeZero m]

abbrev Color := {a : ZMod m // a ≠ 0}

def point (u : Color m → K) (h : ZMod m → Kˣ) (a : Color m) (x : ZMod m) : K :=
  u a * (h x).val / (h (a.val+x)).val

theorem character_rescaling (u : Color m → K) (h g : ZMod m → Kˣ)
    (χ : ZMod m → Kˣ) (hg : ∀ x,g x=h x*χ x)
    (hχ : ∀ a x,χ (a+x)=χ a*χ x) (a : Color m) (x : ZMod m) :
    point m u g a x = (u a/(χ a.val).val) * (h x).val/(h (a.val+x)).val := by
  unfold point
  rw [hg x,hg (a.val+x),hχ]
  simp only [Units.val_mul]
  field_simp
  <;> ring

/-- Complete row recovery over an arbitrary field once the two summands
of the shift-one row are aligned. -/
theorem all_rows_of_aligned_one
    (one : Color m) (hone : one.val=1)
    (u v : Bool → Color m → K) (h g : Bool → ZMod m → Kˣ)
    (hb : ∀ b,h b 0=1) (gb : ∀ b,g b 0=1)
    (hu : ∀ b,u b one ≠ 0) (hv : ∀ b,v b one ≠ 0)
    (hrow : ∀ b x,point m (u b) (h b) one x=point m (v b) (g b) one x)
    (hobs : ∀ a : Color m, ∀ x : ZMod m, x=0 ∨ x= -a.val →
      point m (u false) (h false) a x+point m (u true) (h true) a x=
      point m (v false) (g false) a x+point m (v true) (g true) a x)
    (hdet : ∀ a : Color m,
      (h true (-a.val)).val/(h false a.val).val-
        (h false (-a.val)).val/(h true a.val).val ≠ 0) :
    ∀ a x,point m (u false) (h false) a x+point m (u true) (h true) a x=
      point m (v false) (g false) a x+point m (v true) (g true) a x := by
  let χ : Bool → ZMod m → Kˣ := fun b x => g b x/h b x
  have hχ (b : Bool) : ∀ a x,χ b (a+x)=χ b a*χ b x := by
    apply CyclicTorusRecovery.quotient_character_of_row (m := m)
      (u b one) (v b one) (hu b) (hv b) (h b) (g b) (hb b) (gb b)
    intro x
    simpa only [point,hone,mul_div_assoc] using hrow b x
  have hg (b : Bool) (x : ZMod m) : g b x=h b x*χ b x := by
    simp [χ,mul_div_cancel_left]
  let w : Bool → Color m → K := fun b a => v b a/(χ b a.val).val
  have hp (b : Bool) (a : Color m) (x : ZMod m) :
      point m (v b) (g b) a x=point m (w b) (h b) a x :=
    character_rescaling m (v b) (h b) (g b) (χ b) (hg b) (hχ b) a x
  have hw (a : Color m) : u false a=w false a ∧ u true a=w true a := by
    apply CyclicTorusRecovery.two_row_coefficients_unique
      ((h false a.val).val)⁻¹ ((h true a.val).val)⁻¹
      (h false (-a.val)).val (h true (-a.val)).val
    · simpa only [div_eq_mul_inv,mul_comm] using hdet a
    · have hh := hobs a 0 (Or.inl rfl)
      rw [hp false a 0,hp true a 0] at hh
      simpa only [point,add_zero,hb,Units.val_one,mul_one,div_eq_mul_inv,mul_comm] using hh
    · have hh := hobs a (-a.val) (Or.inr rfl)
      rw [hp false a (-a.val),hp true a (-a.val)] at hh
      simpa only [point,add_neg_cancel,hb,Units.val_one,div_one,mul_comm] using hh
  intro a x
  rw [hp false a x,hp true a x]
  simp only [point,(hw a).1,(hw a).2]

end Sunlet.CyclicCompleteRecovery
end
end Stage_CyclicCompleteRecovery
#check "SUNLET_VERIFIEDCYCLICFIELD_CyclicCompleteRecovery_DONE"

section Stage_CyclicBirational


/-!
# Recovery from the literal cyclic coordinate set

The retained off-diagonal coordinates generate the entire image field.
The argument works over the original characteristic-zero field: every
embedding fixing the observations aligns the two five-color summands,
the color-one row determines the character ambiguity, and the two retained
entries solve the remaining rows. Fixed-field descent then gives rational
recovery, rather than merely recovery after adjoining algebraic parameters.
-/

noncomputable section

namespace Sunlet.CyclicSelectedField

open ToricPairAlgebra

variable {k : Type*} [Field k] [CharZero k] (m : ℕ) [NeZero m]

lemma bool_sum_equiv {A : Type*} [AddCommMonoid A] (σ : Equiv.Perm Bool) (f : Bool → A) :
    f (σ false) + f (σ true) = f false + f true := by
  have hne : σ false ≠ σ true := σ.injective.ne Bool.false_ne_true
  cases h0 : σ false <;> cases h1 : σ true <;> simp_all [add_comm]

lemma embedded_cyclic_point {A : Type*} [Field A] [CharZero A] [Algebra k A]
    (φ : FullField (k := k) m →ₐ[k] A) (b : Bool) (a : Color m) (x : ZMod m) :
    CyclicCompleteRecovery.point m (embeddedCoefficient 0 φ b) (embeddedTorus 0 φ b) a x =
      φ (genericPoint 0 (permutation m) b (a,x)) := by
  have hh := congrFun (embedded_point (0 : ZMod m) φ (permutation m) b) (a,x)
  simpa only [CyclicCompleteRecovery.point, toricPoint, ToricDifferential.coordinate,
    ToricDifferential.ratio, permutation, Equiv.coe_addLeft, mul_div_assoc] using hh

theorem all_coordinates_of_one_alignment {A : Type*} [Field A] [CharZero A] [Algebra k A]
    (hm : 6 ≤ m) (φ ψ : FullField (k := k) m →ₐ[k] A) (σ : Equiv.Perm Bool)
    (halign : ∀ b x,
      φ (genericPoint 0 (permutation m) b (colorEmbedding m hm 0,x)) =
        ψ (genericPoint 0 (permutation m) (σ b) (colorEmbedding m hm 0,x)))
    (hobs : ∀ ax : Color m × ZMod m, Retained m hm ax →
      φ (genericCoordinates 0 (permutation m) ax) =
        ψ (genericCoordinates 0 (permutation m) ax)) :
    ∀ ax : Color m × ZMod m,
      φ (genericCoordinates 0 (permutation m) ax) =
        ψ (genericCoordinates 0 (permutation m) ax) := by
  have hone : (colorEmbedding m hm 0).val = (1 : ZMod m) :=
    CyclicSparseWitness.shift_zero m
  have htorus (b : Bool) (x : ZMod m) :
      (embeddedTorus (0 : ZMod m) φ b x : A) =
        φ (genericTorus (k := k) (ι := Color m) (0 : ZMod m) b x).val := rfl
  have hr := CyclicCompleteRecovery.all_rows_of_aligned_one m
    (colorEmbedding m hm 0) hone
    (embeddedCoefficient 0 φ) (fun b => embeddedCoefficient 0 ψ (σ b))
    (embeddedTorus 0 φ) (fun b => embeddedTorus 0 ψ (σ b))
    (embeddedTorus_base 0 φ) (fun b => embeddedTorus_base 0 ψ (σ b))
    (fun b => embeddedCoefficient_ne_zero 0 φ b _)
    (fun b => embeddedCoefficient_ne_zero 0 ψ (σ b) _)
    (by
      intro b x
      rw [embedded_cyclic_point, embedded_cyclic_point]
      exact halign b x)
    (by
      intro a x hx
      simp only [embedded_cyclic_point]
      rw [bool_sum_equiv σ (fun b => ψ (genericPoint 0 (permutation m) b (a,x))),
        ← map_add, ← map_add]
      exact hobs (a,x) (Or.inr hx))
    (by
      intro a
      have hh := (map_ne_zero φ).2 (rowDeterminant_ne_zero (k := k) m a)
      simpa only [rowDeterminant, map_sub, map_div₀, htorus] using hh)
  rintro ⟨a,x⟩
  have hh := hr a x
  simp only [embedded_cyclic_point] at hh
  rw [bool_sum_equiv σ (fun b => ψ (genericPoint 0 (permutation m) b (a,x))),
    ← map_add, ← map_add] at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
theorem coordinates_fixed_by_observed_embeddings (hm : 6 ≤ m)
    (ψ : FullField (k := k) m →ₐ[ObservedField (k := k) m hm]
      AlgebraicClosure (FullField (k := k) m)) :
    ∀ ax, ψ (genericCoordinates 0 (permutation m) ax) =
      algebraMap (FullField (k := k) m) (AlgebraicClosure (FullField (k := k) m))
        (genericCoordinates 0 (permutation m) ax) := by
  let E := FullField (k := k) m
  let S := SmallField (k := k) m
  let A := AlgebraicClosure E
  let φ : E →ₐ[k] A := IsScalarTower.toAlgHom k E A
  let ψk : E →ₐ[k] A := ψ.restrictScalars k
  let i : S →ₐ[k] E := inclusion m hm
  let j : S →ₐ[k] A := φ.comp i
  letI : Algebra S A := j.toRingHom.toAlgebra
  letI : IsScalarTower k S A := IsScalarTower.of_algebraMap_eq fun c => (j.commutes c).symm
  have hobs : ∀ ax : Color m × ZMod m, Retained m hm ax →
      φ (genericCoordinates 0 (permutation m) ax) =
        ψk (genericCoordinates 0 (permutation m) ax) := by
    intro ax hx
    let q : ObservedField (k := k) m hm :=
      ⟨genericCoordinates 0 (permutation m) ax, observed_mem m hm ax hx⟩
    exact (ψ.commutes q).symm
  have hcoord : ∀ ax,
      algebraMap S A (genericCoordinates 0 (CyclicSparseWitness.permutation m) ax) =
        (ψk.comp i) (genericCoordinates 0 (CyclicSparseWitness.permutation m) ax) := by
    rintro ⟨a,x⟩
    change φ (i (genericCoordinates 0 (CyclicSparseWitness.permutation m) (a,x))) =
      ψk (i (genericCoordinates 0 (CyclicSparseWitness.permutation m) (a,x)))
    have hiq := inclusion_coordinate (k := k) m hm a x
    exact (congrArg φ hiq).trans
      ((hobs (colorEmbedding m hm a,x) (Or.inl ⟨a,rfl⟩)).trans
        (congrArg ψk hiq).symm)
  have hdim : 2 < Fintype.card (NormalizedVariations.Index (Fin 5) (ZMod m) 0) := by
    simp only [NormalizedVariations.Index, Fintype.card_sum, Fintype.card_fin]
    omega
  have hu := unordered_under_embedding_arbitrary_ambient
    (0 : ZMod m) (CyclicSparseWitness.permutation m)
    (CyclicSparseWitness.witness (k := k) m hm)
    (fun a => CyclicSparseWitness.derangement m hm a 0)
    hdim (ψk.comp i) hcoord
  have hip (b : Bool) (x : ZMod m) :
      i (genericPoint (k := k) (0 : ZMod m) (CyclicSparseWitness.permutation m) b (0,x)) =
        genericPoint (k := k) (0 : ZMod m) (permutation m) b (colorEmbedding m hm 0,x) :=
    inclusion_point (k := k) m hm b 0 x
  have hfull : ∀ ax : Color m × ZMod m,
      φ (genericCoordinates 0 (permutation m) ax) =
        ψk (genericCoordinates 0 (permutation m) ax) := by
    rcases hu with ⟨h0,h1⟩ | ⟨h0,h1⟩
    · apply all_coordinates_of_one_alignment m hm φ ψk (Equiv.refl Bool) ?_ hobs
      intro b x
      cases b
      · have hh := congrFun h0 (0,x)
        change ψk (i _) = φ (i _) at hh
        exact (congrArg φ (hip false x)).symm.trans
          (hh.symm.trans (congrArg ψk (hip false x)))
      · have hh := congrFun h1 (0,x)
        change ψk (i _) = φ (i _) at hh
        exact (congrArg φ (hip true x)).symm.trans
          (hh.symm.trans (congrArg ψk (hip true x)))
    · apply all_coordinates_of_one_alignment m hm φ ψk (Equiv.swap false true) ?_ hobs
      intro b x
      cases b
      · have hh := congrFun h1 (0,x)
        change ψk (i _) = φ (i _) at hh
        exact (congrArg φ (hip false x)).symm.trans
          (hh.symm.trans (congrArg ψk (hip true x)))
      · have hh := congrFun h0 (0,x)
        change ψk (i _) = φ (i _) at hh
        exact (congrArg φ (hip true x)).symm.trans
          (hh.symm.trans (congrArg ψk (hip false x)))
  intro ax
  exact (hfull ax).symm

/-- Every full off-diagonal coordinate is a rational function of exactly
the observed five rows and two entries of each other row. -/
theorem full_coordinate_mem_observed (hm : 6 ≤ m) (ax : Color m × ZMod m) :
    genericCoordinates (k := k) 0 (permutation m) ax ∈ ObservedField (k := k) m hm := by
  letI := full_isAlgebraic (k := k) m hm
  obtain ⟨q,hq⟩ := EmbeddingFixedField.mem_range_of_embeddings
    (F := ObservedField (k := k) m hm)
    (genericCoordinates (k := k) 0 (permutation m) ax)
    (fun ψ => coordinates_fixed_by_observed_embeddings m hm ψ ax)
  exact hq ▸ q.property

/-- Equality of the actual generated function fields, over any
characteristic-zero base field and hence over ℚ. -/
theorem observedField_eq_fullImageField (hm : 6 ≤ m) :
    ObservedField (k := k) m hm =
      JacobianFinite.generatedField (genericCoordinates (k := k) 0 (permutation m)) := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨ax,rfl⟩
    exact JacobianFinite.coordinate_mem_generatedField _ ax.val
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨ax,rfl⟩
    exact full_coordinate_mem_observed m hm ax

end Sunlet.CyclicSelectedField
end
end Stage_CyclicBirational
#check "SUNLET_VERIFIEDCYCLICFIELD_CyclicBirational_DONE"

section Stage_CyclicObservedCoordinates


/-!
# The literal coordinate set in Theorem 6.1

The five complete nonzero rows are 1, 2, −1, 3, −2. Every other
nonzero row contributes precisely its two entries at 0 and −a.
Together with the complete zero row, this gives exactly 8m − 12
coordinates, including at m = 6 where there are no omitted rows.
-/

noncomputable section

namespace Sunlet.CyclicSelectedField

variable (m : ℕ) [NeZero m]

abbrev MissingColor (hm : 6 ≤ m) :=
  {a : Color m // a ∉ Set.range (colorEmbedding m hm)}

noncomputable instance observedFintype (hm : 6 ≤ m) : Fintype (Observed m hm) :=
  Fintype.ofFinite _

noncomputable instance missingColorFintype (hm : 6 ≤ m) : Fintype (MissingColor m hm) :=
  Fintype.ofFinite _

/-- A list without repetition of the observed off-diagonal coordinates. -/
def observationEnumeration (hm : 6 ≤ m) :
    (Fin 5 × ZMod m) ⊕ (MissingColor m hm × Bool) → Observed m hm
  | .inl (a,x) => ⟨(colorEmbedding m hm a,x),Or.inl ⟨a,rfl⟩⟩
  | .inr (a,b) => ⟨(a.val,if b then -a.val.val else 0),by
      cases b
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)⟩

theorem observationEnumeration_injective (hm : 6 ≤ m) :
    Function.Injective (observationEnumeration m hm) := by
  rintro (⟨a,x⟩ | ⟨a,b⟩) (⟨c,y⟩ | ⟨c,d⟩) h
  · have h' := congrArg Subtype.val h
    change (colorEmbedding m hm a,x) = (colorEmbedding m hm c,y) at h'
    have ha := colorEmbedding_injective m hm (congrArg Prod.fst h')
    have hx : x = y := congrArg Prod.snd h'
    simp only [ha,hx]
  · have h' := congrArg (fun q : Observed m hm => q.val.1) h
    exact (c.property ⟨a,h'⟩).elim
  · have h' := congrArg (fun q : Observed m hm => q.val.1) h
    exact (a.property ⟨c,h'.symm⟩).elim
  · have ha : a = c := Subtype.ext (congrArg (fun q : Observed m hm => q.val.1) h)
    subst c
    have hb := congrArg (fun q : Observed m hm => q.val.2) h
    have hbd : b=d := by
      cases b <;> cases d
      · rfl
      · have hz : (0 : ZMod m)= -a.val.val := hb
        exact (a.val.property (neg_eq_zero.mp hz.symm)).elim
      · have hz : -a.val.val=(0 : ZMod m) := hb
        exact (a.val.property (neg_eq_zero.mp hz)).elim
      · rfl
    subst d
    rfl

theorem observationEnumeration_surjective (hm : 6 ≤ m) :
    Function.Surjective (observationEnumeration m hm) := by
  rintro ⟨⟨a,x⟩,hx⟩
  classical
  by_cases ha : a ∈ Set.range (colorEmbedding m hm)
  · obtain ⟨i,rfl⟩ := ha
    exact ⟨.inl (i,x),rfl⟩
  · rcases hx with h | h | h
    · exact (ha h).elim
    · change x = 0 at h
      subst x
      exact ⟨.inr (⟨a,ha⟩,false),rfl⟩
    · change x = -a.val at h
      subst x
      exact ⟨.inr (⟨a,ha⟩,true),rfl⟩

def observationEquiv (hm : 6 ≤ m) :
    (Fin 5 × ZMod m) ⊕ (MissingColor m hm × Bool) ≃ Observed m hm :=
  Equiv.ofBijective (observationEnumeration m hm)
    ⟨observationEnumeration_injective m hm,observationEnumeration_surjective m hm⟩

theorem color_card : Fintype.card (Color m) = m-1 := by
  simpa only [Color,Fintype.card_subtype_compl,Fintype.card_subtype_eq,ZMod.card]
    using Fintype.card_subtype_compl (fun a : ZMod m => a=0)

theorem missingColor_card (hm : 6 ≤ m) : Fintype.card (MissingColor m hm) = m-6 := by
  classical
  have hcard : Fintype.card (Set.range (colorEmbedding m hm)) = 5 := by
    simpa only [Fintype.card_fin] using
      Fintype.card_congr (Equiv.ofInjective _ (colorEmbedding_injective m hm)).symm
  change Fintype.card {a : Color m // a ∉ Set.range (colorEmbedding m hm)} = m - 6
  rw [Fintype.card_subtype_compl,color_card m,hcard]
  omega

theorem observed_card (hm : 6 ≤ m) : Fintype.card (Observed m hm) = 7*m-12 := by
  rw [← Fintype.card_congr (observationEquiv m hm),Fintype.card_sum,
    Fintype.card_prod,Fintype.card_prod,Fintype.card_fin,ZMod.card,
    missingColor_card m hm,Fintype.card_bool]
  omega

/-- The indexing set including the full diagonal row. -/
abbrev FullObserved (hm : 6 ≤ m) := (ZMod m) ⊕ Observed m hm

theorem fullObserved_card (hm : 6 ≤ m) :
    Fintype.card (FullObserved m hm) = 8*m-12 := by
  change Fintype.card ((ZMod m) ⊕ Observed m hm) = 8*m-12
  rw [Fintype.card_sum,ZMod.card,observed_card m hm]
  omega

/-- The paper's displayed coordinate condition, on the pair (a,b)
corresponding to the actual flow triple (a,b,−a−b). -/
def LiteralRetained (ab : ZMod m × ZMod m) : Prop :=
  ab.1=0 ∨ ab.1=1 ∨ ab.1=2 ∨ ab.1= -1 ∨ ab.1=3 ∨ ab.1= -2 ∨
    ab.2=0 ∨ ab.2= -ab.1

theorem color_mem_range_iff (hm : 6 ≤ m) (a : Color m) :
    a ∈ Set.range (colorEmbedding m hm) ↔
      a.val=1 ∨ a.val=2 ∨ a.val= -1 ∨ a.val=3 ∨ a.val= -2 := by
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp [colorEmbedding,CyclicSparseWitness.shift_two m hm,
      CyclicSparseWitness.shift_four m hm]
  · intro h
    rcases h with h | h | h | h | h
    · exact ⟨0,Subtype.ext (by simpa [colorEmbedding] using h.symm)⟩
    · exact ⟨1,Subtype.ext (by simpa [colorEmbedding] using h.symm)⟩
    · exact ⟨2,Subtype.ext (by simpa [colorEmbedding,CyclicSparseWitness.shift_two m hm] using h.symm)⟩
    · exact ⟨3,Subtype.ext (by simpa [colorEmbedding] using h.symm)⟩
    · exact ⟨4,Subtype.ext (by simpa [colorEmbedding,CyclicSparseWitness.shift_four m hm] using h.symm)⟩

def fullObservationIndex (hm : 6 ≤ m) : FullObserved m hm → ZMod m × ZMod m
  | .inl b => (0,b)
  | .inr ab => (ab.val.1.val,ab.val.2)

theorem fullObservationIndex_injective (hm : 6 ≤ m) :
    Function.Injective (fullObservationIndex m hm) := by
  rintro (x | ⟨⟨a,x⟩,hx⟩) (y | ⟨⟨b,y⟩,hy⟩) h
  · exact congrArg Sum.inl (congrArg Prod.snd h)
  · exact (b.property (congrArg Prod.fst h).symm).elim
  · exact (a.property (congrArg Prod.fst h)).elim
  · change (a.val,x) = (b.val,y) at h
    have hab : a = b := Subtype.ext (congrArg (fun p : ZMod m × ZMod m => p.1) h)
    have hxy : x = y := congrArg (fun p : ZMod m × ZMod m => p.2) h
    subst b
    subst y
    rfl

theorem fullObservationIndex_range (hm : 6 ≤ m) :
    Set.range (fullObservationIndex m hm) = {ab | LiteralRetained m ab} := by
  ext ⟨a,b⟩
  constructor
  · rintro ⟨x,hx⟩
    rcases x with x | ⟨⟨c,x⟩,hc⟩
    · cases hx
      exact Or.inl rfl
    · cases hx
      change c.val=0 ∨ _
      right
      rcases hc with h | h | h
      · rcases (color_mem_range_iff m hm c).mp h with h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  · intro h
    by_cases ha : a=0
    · subst a
      exact ⟨.inl b,rfl⟩
    · refine ⟨.inr ⟨(⟨a,ha⟩,b),?_⟩,rfl⟩
      change a=0 ∨ _ at h
      rcases h with h | h | h | h | h | h | h | h
      · exact (ha h).elim
      · exact Or.inl ((color_mem_range_iff m hm ⟨a,ha⟩).mpr (Or.inl h))
      · exact Or.inl ((color_mem_range_iff m hm ⟨a,ha⟩).mpr (Or.inr (Or.inl h)))
      · exact Or.inl ((color_mem_range_iff m hm ⟨a,ha⟩).mpr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inl ((color_mem_range_iff m hm ⟨a,ha⟩).mpr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inl ((color_mem_range_iff m hm ⟨a,ha⟩).mpr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

end Sunlet.CyclicSelectedField
end
end Stage_CyclicObservedCoordinates
#check "SUNLET_VERIFIEDCYCLICFIELD_CyclicObservedCoordinates_DONE"

#check Sunlet.CyclicSelectedField.full_isAlgebraic
#print axioms Sunlet.CyclicSelectedField.full_isAlgebraic

#check Sunlet.CyclicSelectedField.full_coordinate_mem_observed
#print axioms Sunlet.CyclicSelectedField.full_coordinate_mem_observed

#check Sunlet.CyclicSelectedField.observedField_eq_fullImageField
#print axioms Sunlet.CyclicSelectedField.observedField_eq_fullImageField

#check Sunlet.CyclicSelectedField.fullObserved_card
#print axioms Sunlet.CyclicSelectedField.fullObserved_card

#check Sunlet.CyclicSelectedField.fullObservationIndex_range
#print axioms Sunlet.CyclicSelectedField.fullObservationIndex_range
