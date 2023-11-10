(** This file is part of [https://github.com/mjub/hott]. *)

(** * Martin-Löf type theory

  Let us write the universes [𝑈] instead of [Type] because, why not? *)

Notation 𝑈₀ := Set.
Notation 𝑈 := Type.

(** ** Dependent function types *)

Notation "∏ x .. y , B" := (forall x, .. (forall y, B) ..)
  (at level 10, x binder, y binder, B at level 200,
  format "'[  ' '[  ' ∏  x  ..  y ']' ,  '/' B ']'").

Notation "A → B" := (∏ _ : A, B)
  (at level 99, B at level 200, right associativity).

Notation "'λ' x .. y , T" := (fun x => .. (fun y => T) ..)
  (at level 10, x binder, y binder, T at level 200,
  format "'[  ' '[  ' 'λ'  x  ..  y ']' ,  '/' T ']'").

(** ** Dependent pair types *)

Inductive Sigma (A : 𝑈) (B : A → 𝑈) : 𝑈 :=
  pair : ∏ x, B x → _.

Arguments pair {_ _}.

Notation "∑ x .. y , B" := (Sigma _ (λ x, .. (Sigma _ (λ y, B)) ..))
  (at level 10, x binder, y binder, B at level 200,
  format "'[  ' '[  ' ∑  x  ..  y ']' ,  '/' B ']'").

Notation "( x , .. , y , z )" := (pair x (.. (pair y z) ..))
  (at level 0, format "( '[' x ,  '/' .. ,  '/' y ,  '/' z ']' )").
