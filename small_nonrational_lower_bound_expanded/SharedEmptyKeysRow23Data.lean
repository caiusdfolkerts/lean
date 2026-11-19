module
prelude
public import GraphRouteCasesData
public import SharedSmallRoots23

@[expose] public section
noncomputable section

@[reducible] def Papers.RationalityTen.SharedEmptyKeys.Row23.offset : Nat :=
6694
def Papers.RationalityTen.SharedEmptyKeys.Row23.rootCode : Fin
    Papers.RationalityTen.SharedSmallRootCertificates.Row23.rootCount →
  Nat :=
fun i => (Papers.RationalityTen.SharedSmallRootCertificates.Row23.entry i).val.snd
def Papers.RationalityTen.SharedEmptyKeys.Row23.test : Nat → Bool :=
fun i =>
  Decidable.decide
    (Papers.RationalityTen.GraphRoutes.emptyRootKeys.entry (Papers.RationalityTen.SharedEmptyKeys.Row23.offset + i) =
      (23,
        Papers.RationalityTen.SharedSmallRootReplay.complement
          (Papers.RationalityTen.SharedEmptyKeys.Row23.rootCode
            (Fin.ofNat Papers.RationalityTen.SharedSmallRootCertificates.Row23.rootCount i))))

