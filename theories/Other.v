Require Import Hello.Main(double_negation).

Theorem refl : double_negation = double_negation.
Proof.
  reflexivity.
Qed.

Fail Check three.
