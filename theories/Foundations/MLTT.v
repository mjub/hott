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

Notation "A × B" := (∑ _ : A, B)
  (at level 40, right associativity).

Notation "( x , .. , y , z )" := (pair x (.. (pair y z) ..))
  (at level 0, format "( '[' x ,  '/' .. ,  '/' y ,  '/' z ']' )").

Section Sigma.
  Context {A : 𝑈} {B : A → 𝑈}.

  Definition sigma_elim (C : (∑ x, B x) → 𝑈) (g : ∏ x (y : B x), C (x, y)) p : C p :=
    match p with pair x y => g x y end.

  Definition pr₁ : (∑ x, B x) → A := sigma_elim _ (λ x _, x).
  Definition pr₂ : ∏ p : ∑ x, B x, B (pr₁ p) := sigma_elim _ (λ _ y, y).
End Sigma.

Notation "p .1" := (pr₁ p)
  (at level 1, left associativity, format "p .1").
Notation "p .2" := (pr₂ p)
  (at level 1, left associativity, format "p .2").
