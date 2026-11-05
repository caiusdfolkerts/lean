module

public import PaperVerification.FermionFormalCoordinates
public import PaperVerification.FermionNilpotentSeriesEval

/-!
# Ramified coordinates and their inverses in nilpotent algebras

The coordinate is constructed in the formal power series domain before being
evaluated in an Artinian algebra. In particular, the cofactor identity is not
obtained by cancelling a nilpotent element after specialization.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open Polynomial
variable {F : Type*} [Field F]

/-- A chosen root of the univariate cofactor in the formal power series ring.
Existence is proved below from algebraic closedness and characteristic zero. -/
structure RamifiedCoordinate (phi : Polynomial F) (rho : F) where
  unit : (PowerSeries F)ˣ
  unit_power :
    (unit : PowerSeries F)^((phi-C (phi.eval rho)).rootMultiplicity rho) =
      Polynomial.aeval (PowerSeries.X+PowerSeries.C rho)
        (rootCofactor (phi-C (phi.eval rho)) rho)

namespace RamifiedCoordinate

variable {phi : Polynomial F} {rho : F}

def series (c : RamifiedCoordinate phi rho) : PowerSeries F :=
  PowerSeries.X * (c.unit : PowerSeries F)

@[simp] theorem constantCoeff_series (c : RamifiedCoordinate phi rho) :
    c.series.constantCoeff=0 := by simp [series]

theorem coeff_one_isUnit (c : RamifiedCoordinate phi rho) :
    IsUnit (c.series.coeff 1) := by
  simpa only [series,PowerSeries.coeff_one_mul,PowerSeries.coeff_one_X,
    PowerSeries.constantCoeff_X,one_mul,mul_zero,add_zero] using
    PowerSeries.isUnit_constantCoeff (c.unit : PowerSeries F) c.unit.isUnit

def inverseSeries (c : RamifiedCoordinate phi rho) : PowerSeries F :=
  c.series.substInvOfIsUnit c.coeff_one_isUnit

@[simp] theorem constantCoeff_inverseSeries (c : RamifiedCoordinate phi rho) :
    c.inverseSeries.constantCoeff=0 :=
  PowerSeries.constantCoeff_substInvOfIsUnit c.series c.coeff_one_isUnit

theorem series_power (c : RamifiedCoordinate phi rho) :
    c.series^((phi-C (phi.eval rho)).rootMultiplicity rho) =
      Polynomial.aeval (PowerSeries.X+PowerSeries.C rho) phi-
        PowerSeries.C (phi.eval rho) := by
  let shift : Polynomial F →ₐ[F] PowerSeries F :=
    Polynomial.aeval (PowerSeries.X+PowerSeries.C rho)
  have he := congrArg shift
    (rootCofactor_factorization (phi-C (phi.eval rho)) rho)
  have he' :
      PowerSeries.X^((phi-C (phi.eval rho)).rootMultiplicity rho) *
        shift (rootCofactor (phi-C (phi.eval rho)) rho) =
      shift (phi-C (phi.eval rho)) := by
    simpa only [shift,map_mul,map_pow,map_sub,Polynomial.aeval_X,
      Polynomial.aeval_C,PowerSeries.algebraMap_eq,add_sub_cancel_right] using he
  rw [series,mul_pow,c.unit_power]
  exact he'.trans (by
    simp only [shift,map_sub,Polynomial.aeval_C,PowerSeries.algebraMap_eq])

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]

def evaluatedUnit (c : RamifiedCoordinate phi rho) (x : A) (hx : IsNilpotent x) : Aˣ :=
  Units.map (nilpotentSeriesEval x hx).toMonoidHom c.unit

def forward (c : RamifiedCoordinate phi rho) (x : A) (hx : IsNilpotent x) : A :=
  nilpotentSeriesEval x hx c.series

def backward (c : RamifiedCoordinate phi rho) (z : A) (hz : IsNilpotent z) : A :=
  nilpotentSeriesEval z hz c.inverseSeries

theorem forward_isNilpotent (c : RamifiedCoordinate phi rho) (x : A) (hx : IsNilpotent x) :
    IsNilpotent (c.forward x hx) :=
  nilpotentSeriesEval_isNilpotent x hx c.series c.constantCoeff_series

theorem backward_isNilpotent (c : RamifiedCoordinate phi rho) (z : A) (hz : IsNilpotent z) :
    IsNilpotent (c.backward z hz) :=
  nilpotentSeriesEval_isNilpotent z hz c.inverseSeries c.constantCoeff_inverseSeries

@[simp] theorem forward_eq_mul_unit (c : RamifiedCoordinate phi rho)
    (x : A) (hx : IsNilpotent x) :
    c.forward x hx=x*c.evaluatedUnit x hx := by
  simp [forward,series,evaluatedUnit]

theorem evaluatedUnit_power (c : RamifiedCoordinate phi rho)
    (x : A) (hx : IsNilpotent x) :
    (c.evaluatedUnit x hx : A)^((phi-C (phi.eval rho)).rootMultiplicity rho) =
      Polynomial.aeval (x+algebraMap F A rho)
        (rootCofactor (phi-C (phi.eval rho)) rho) := by
  have he := congrArg (nilpotentSeriesEval x hx) c.unit_power
  simpa only [evaluatedUnit,Units.coe_map,RingHom.toMonoidHom_eq_coe,
    AlgHom.toRingHom_eq_coe,AlgHom.toRingHom_toMonoidHom,
    AlgHom.coe_toMonoidHom,AlgHom.coe_toRingHom,map_pow,←Polynomial.aeval_algHom_apply,
    map_add,nilpotentSeriesEval_X,nilpotentSeriesEval_C] using he

theorem forward_power (c : RamifiedCoordinate phi rho)
    (x : A) (hx : IsNilpotent x) :
    (c.forward x hx)^((phi-C (phi.eval rho)).rootMultiplicity rho) =
      Polynomial.aeval (x+algebraMap F A rho) phi-algebraMap F A (phi.eval rho) := by
  have he := congrArg (nilpotentSeriesEval x hx) c.series_power
  simpa only [forward,map_pow,map_sub,←Polynomial.aeval_algHom_apply,
    map_add,nilpotentSeriesEval_X,nilpotentSeriesEval_C] using he

@[simp] theorem backward_forward (c : RamifiedCoordinate phi rho)
    (x : A) (hx : IsNilpotent x) :
    c.backward (c.forward x hx) (c.forward_isNilpotent x hx)=x :=
  nilpotentSeriesEval_subst_inverse x hx c.series c.constantCoeff_series c.coeff_one_isUnit

@[simp] theorem forward_backward (c : RamifiedCoordinate phi rho)
    (z : A) (hz : IsNilpotent z) :
    c.forward (c.backward z hz) (c.backward_isNilpotent z hz)=z :=
  nilpotentSeriesEval_inverse_subst z hz c.series c.constantCoeff_series c.coeff_one_isUnit

/-- The inverse coordinate gives an exact solution of the separated cover
equation, not merely an equality modulo the maximal ideal. -/
theorem cover_backward (c : RamifiedCoordinate phi rho)
    (z : A) (hz : IsNilpotent z) :
    Polynomial.aeval (c.backward z hz+algebraMap F A rho) phi =
      algebraMap F A (phi.eval rho)+
        z^((phi-C (phi.eval rho)).rootMultiplicity rho) := by
  have he := c.forward_power (c.backward z hz) (c.backward_isNilpotent z hz)
  rw [c.forward_backward] at he
  exact (sub_eq_iff_eq_add.mp he.symm).trans (add_comm _ _)

/-- Coordinate evaluation is natural in the actual coefficient algebra. -/
theorem forward_map (c : RamifiedCoordinate phi rho) (x : A) (hx : IsNilpotent x)
    (f : A →ₐ[F] B) :
    f (c.forward x hx)=c.forward (f x) (hx.map f.toRingHom) :=
  AlgHom.congr_fun (nilpotentSeriesEval_map x hx f) c.series

theorem backward_map (c : RamifiedCoordinate phi rho) (z : A) (hz : IsNilpotent z)
    (f : A →ₐ[F] B) :
    f (c.backward z hz)=c.backward (f z) (hz.map f.toRingHom) :=
  AlgHom.congr_fun (nilpotentSeriesEval_map z hz f) c.inverseSeries

end RamifiedCoordinate

variable [CharZero F] [IsAlgClosed F]

/-- Existence uses only the actual cover polynomial, its root, and the
stated field hypotheses. It assumes neither a local isomorphism nor a basis. -/
theorem exists_ramifiedCoordinate (phi : Polynomial F) (rho : F)
    (hphi : phi-C (phi.eval rho)≠0) :
    Nonempty (RamifiedCoordinate phi rho) := by
  let p := phi-C (phi.eval rho)
  let r := p.rootMultiplicity rho
  let q := rootCofactor p rho
  let shift : Polynomial F →ₐ[F] PowerSeries F :=
    Polynomial.aeval (PowerSeries.X+PowerSeries.C rho)
  have hr : 0<r :=
    (Polynomial.rootMultiplicity_pos hphi).mpr (by simp [p,Polynomial.IsRoot])
  have hq : q.eval rho≠0 := rootCofactor_eval_ne_zero p hphi rho
  have hres : powerSeriesResidue (shift q)=q.eval rho := by
    rw [←Polynomial.aeval_algHom_apply]
    change Polynomial.aeval
      (PowerSeries.constantCoeff (PowerSeries.X+PowerSeries.C rho)) q=q.eval rho
    rw [map_add,PowerSeries.constantCoeff_X,PowerSeries.constantCoeff_C,zero_add]
    simp only [Polynomial.aeval_def,Algebra.algebraMap_self,Polynomial.eval₂_id]
  have hu : IsUnit (shift q) :=
    (unit_iff_residue_ne_zero powerSeriesResidue _).mpr (hres.symm ▸ hq)
  obtain ⟨v,hv,hvu⟩ := exists_powerSeries_unit_root (shift q) hu r hr
  exact ⟨⟨hvu.unit,by simpa only [hvu.unit_spec] using hv⟩⟩

def ramifiedCoordinate (phi : Polynomial F) (rho : F)
    (hphi : phi-C (phi.eval rho)≠0) : RamifiedCoordinate phi rho :=
  Classical.choice (exists_ramifiedCoordinate phi rho hphi)

end PaperVerification.Fermion
