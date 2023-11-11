(** This file is part of [https://github.com/mjub/hott]. *)


(** * Martin-Löf Type Theory, Part I: The Essentials

  ** Universes

  Let us write the universes [𝑈] instead of [Type] because, why not? *)

Notation 𝑈₀ := Set.
Notation 𝑈 := Type.


(** ** Dependent function types

  Dependent function types, or [∏]-types.

  The notation level and format was extracted from the Coq standard library. *)

Notation "∏ x .. y , B" := (forall x, .. (forall y, B) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' ∏  x  ..  y ']' ,  '/' B ']'").

(** Nondependent version, i.e. ordinary functions [A → B]. *)

Notation "A → B" := (∏ _ : A, B)
  (at level 99, B at level 200, right associativity).

(** [λ]-abstractions. *)

Notation "'λ' x .. y , T" := (fun x => .. (fun y => T) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' 'λ'  x  ..  y ']' ,  '/' T ']'").


(** ** Dependent pair types

  Dependent pair types, or [∑]-types.

  I write [pair] instead of [exist] because I find it unequivocal. The notations were, again, extracted from the Coq standard library.

  I may change the definition to [Record] in the future so that I can make use of [Primitive Projections]. *)

Inductive Sigma (A : 𝑈) (B : A → 𝑈) : 𝑈 :=
  pair : ∏ x, B x → _.

Arguments pair {_ _}.

Notation "∑ x .. y , B" := (Sigma _ (λ x, .. (Sigma _ (λ y, B)) ..))
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' ∑  x  ..  y ']' ,  '/' B ']'").

Notation "( x , .. , y , z )" := (pair x (.. (pair y z) ..))
  (at level 0, format "( '[' x ,  '/' .. ,  '/' y ,  '/' z ']' )").

(** Nondependent version, i.e. ordinary cartesian product [A × B]. *)

Notation "A × B" := (∑ _ : A, B)
  (at level 40, right associativity).

(** Elimination principles for [∑]-types. *)

Section Sigma.
  Context {A : 𝑈} {B : A → 𝑈}.

  Definition ind_sigma (C : (∑ x, B x) → 𝑈) (f : ∏ x (y : B x), C (x, y)) p :=
    match p with
    | pair x y => f x y
    end.

  Definition rec_sigma {C : 𝑈} (f : ∏ x, B x → C) p :=
    match p with
    | pair x y => f x y
    end.

  (** Projections. *)

  Definition pr₁ (p : ∑ x, B x) :=
    match p with
    | pair x y => x
    end.

  Definition pr₂ (p : ∑ x, B x) : B (pr₁ p) :=
    match p with
    | pair x y => y
    end.

End Sigma.

Notation "p .1" := (pr₁ p)
  (at level 1, left associativity, format "p .1").
Notation "p .2" := (pr₂ p)
  (at level 1, left associativity, format "p .2").


(** ** Identity types

  I write [Id] instead of [Path] because I hold the controversial opinion that we should not think of types as spaces. *)

Inductive Id {A : 𝑈} (x : A) : A → 𝑈 :=
  refl : Id x x.

Arguments refl {_ _}.

Notation "x = y" := (Id x y)
  (at level 70, no associativity).

(** Elimination principles for identity types. *)

Section Id.
  Context {A : 𝑈} {x : A}.

  Definition ind_id (C : ∏ y, x = y → 𝑈) (c₀ : C x refl) {y : A} (p : x = y) :=
    match p with
    | refl => c₀
    end.

  Definition rec_id {C : 𝑈} (c₀ : C) {y : A} (p : x = y) :=
    match p with
    | refl => c₀
    end.

End Id.
