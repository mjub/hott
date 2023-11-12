(** This file is part of [https://github.com/mjub/hott]. *)

Require Export Foundations.MLTT.Init.


(** * Martin-Löf Type Theory, Part III: The Natural Numbers

  ** Definition *)

Inductive ℕ : 𝑈₀ := zero | succ : ℕ → ℕ.

Notation "0" := zero.

Notation "n + 1" := (succ n)
  (at level 2, left associativity, format "n  +  1").
Notation "n + 2" := (succ (succ n))
  (at level 2, left associativity, format "n  +  2").
Notation "n + 3" := (succ (succ (succ n)))
  (at level 2, left associativity, format "n  +  3").

(** Elimination principles for the natural numbers. *)

Fixpoint ind_ℕ (C : ℕ → 𝑈) (c₀ : C 0) (cₛ : ∏ n, C n → C (n + 1)) n :=
  match n with
  | 0 => c₀
  | k + 1 => cₛ k (ind_ℕ _ c₀ cₛ k)
  end.

Fixpoint rec_ℕ {C : 𝑈} (c₀ : C) (cₛ : ∏ n, C → C) n :=
  match n with
  | 0 => c₀
  | k + 1 => cₛ k (rec_ℕ c₀ cₛ k)
  end.


(** ** Dirty hack

  I am not smart enough to understand how to use [Number Notation]... *)

Notation "1" := (succ 0).
Notation "2" := (succ 1).
Notation "3" := (succ 2).
Notation "4" := (succ 3).
Notation "5" := (succ 4).
Notation "6" := (succ 5).
Notation "7" := (succ 6).
Notation "8" := (succ 7).
Notation "9" := (succ 8).
