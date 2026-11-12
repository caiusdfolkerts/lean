module

public import ToricPower.PeriodicMain

/-!
The definitions in this file deliberately lie outside any noncomputable section.
Their accepted executable bodies certify that the determinant period and the
uniform threshold use only finite integer computations. The equality lemmas
connect these programs to the constants in the proved statements.
-/

@[expose] public section

namespace ToricPower

variable {n s : ℕ}

def executableRayPeriod (A : Matrix (Fin s) (Fin n) ℤ) : ℕ := rayPeriod A

def executableRayThresholdCoefficient (A : Matrix (Fin s) (Fin n) ℤ) : ℕ :=
  rayThresholdCoefficient A

def executableDivisorHeight (b : Fin s → ℤ) : ℕ := divisorHeight b

def executablePeriodicityBound (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ) : ℕ :=
  periodicityBound A b

@[simp] theorem executableRayPeriod_eq (A : Matrix (Fin s) (Fin n) ℤ) :
    executableRayPeriod A = rayPeriod A := rfl

@[simp] theorem executableRayThresholdCoefficient_eq (A : Matrix (Fin s) (Fin n) ℤ) :
    executableRayThresholdCoefficient A = rayThresholdCoefficient A := rfl

@[simp] theorem executableDivisorHeight_eq (b : Fin s → ℤ) :
    executableDivisorHeight b = divisorHeight b := rfl

@[simp] theorem executablePeriodicityBound_eq (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ) :
    executablePeriodicityBound A b = periodicityBound A b := rfl

end ToricPower
