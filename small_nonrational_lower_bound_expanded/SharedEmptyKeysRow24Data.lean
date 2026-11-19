module
prelude
public import GraphRouteCasesData
public import SharedSmallRoots24

@[expose] public section
noncomputable section

@[reducible] def Papers.RationalityTen.SharedEmptyKeys.Row24.offset : Nat :=
8209
def Papers.RationalityTen.SharedEmptyKeys.Row24.rootCode : Fin
    Papers.RationalityTen.SharedSmallRootCertificates.Row24.rootCount →
  Nat :=
fun i => (Papers.RationalityTen.SharedSmallRootCertificates.Row24.entry i).val.snd
def Papers.RationalityTen.SharedEmptyKeys.Row24.test : Nat → Bool :=
fun i =>
  Decidable.decide
    (Papers.RationalityTen.GraphRoutes.emptyRootKeys.entry (Papers.RationalityTen.SharedEmptyKeys.Row24.offset + i) =
      (24,
        Papers.RationalityTen.SharedSmallRootReplay.complement
          (Papers.RationalityTen.SharedEmptyKeys.Row24.rootCode
            (Fin.ofNat Papers.RationalityTen.SharedSmallRootCertificates.Row24.rootCount i))))

