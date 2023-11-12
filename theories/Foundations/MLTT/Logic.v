(** This file is part of [https://github.com/mjub/hott]. *)

Require Export Foundations.MLTT.Init.


(** * Martin-Löf Type Theory, Part II: The Logic

  ** The empty type

  The [Empty] type, also known as [False]. *)

Inductive Empty : 𝑈₀ := .

Notation "∅" := Empty.

(** Elimination principles for the empty type. *)

Definition ind_empty (C : ∅ → 𝑈) x : C x :=
  match x with
  end.

Definition rec_empty {C : 𝑈} (x : ∅) : C :=
  match x with
  end.


(** ** The unit type

  The [Unit] type, also known as [True]. *)

Inductive Unit : 𝑈₀ := it.

Notation "𝟏" := Unit.
Notation "∗" := it.

(** Elimination principles for the unit type. *)

Definition ind_unit (C : 𝟏 → 𝑈) (c₀ : C ∗) x :=
  match x with
  | ∗ => c₀
  end.

Definition rec_unit {C : 𝑈} (c₀ : C) x :=
  match x with
  | ∗ => c₀
  end.


(** ** Product types

  This is the nondependent version of [∑]-types, i.e. ordinary cartesian product [A × B]. *)

Notation "A × B" := (∑ (_ : A), B)
  (at level 40, right associativity).

(** Elimination principles for product types. *)

Section Prod.
  Context {A B : 𝑈}.

  Definition ind_prod (C : A × B → 𝑈) (f : ∏ (x : A) (y : B), C (x, y)) p :=
    match p with
    | (x, y) => f x y
    end.

  Definition rec_prod {C : 𝑈} (f : A → B → C) (p : A × B) :=
    match p with
    | (x, y) => f x y
    end.

End Prod.


(** ** Coproduct types

  The disjoint union [A + B] of two types [A], [B]. *)

Inductive Coprod (A B : 𝑈) : 𝑈 := inl : A → _ | inr : B → _.

Arguments inl {_ _}.
Arguments inr {_ _}.

Notation "A + B" := (Coprod A B)
  (at level 50, right associativity).

(** Elimination principles for coproduct types. *)

Section Coprod.
  Context {A B : 𝑈}.

  Definition ind_coprod (C : A + B → 𝑈) (f : ∏ x, C (inl x)) (g : ∏ y, C (inr y)) p :=
    match p with
    | inl x => f x
    | inr y => g y
    end.

  Definition rec_coprod {C : 𝑈} (f : A → C) (g : B → C) p :=
    match p with
    | inl x => f x
    | inr y => g y
    end.

End Coprod.


(** ** The type of booleans

  The type of [Bool]eans, which could alternatively be defined as [𝟏 + 𝟏] (see above). *)

Inductive Bool : 𝑈₀ := true | false.

(** Elimination principles for the type of booleans. *)

Definition ind_bool (C : Bool → 𝑈) (c₀ : C true) (c₁ : C false) b :=
  match b with
  | true => c₀
  | false => c₁
  end.

Definition rec_bool {C : 𝑈} (c₀ c₁ : C) b :=
  match b with
  | true => c₀
  | false => c₁
  end.
