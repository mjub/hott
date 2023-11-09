Require Import Utf8.

Theorem double_negation : ∀ P : Prop, ¬ ¬ ¬ P -> ¬ P.
Proof.
  intuition.
Qed.

Definition three := 3.
