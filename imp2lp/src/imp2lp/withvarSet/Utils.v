From Stdlib Require Import List.

Import ListNotations.

(* Utilities shared by the two compiler phases *)

(* Apply [f] to each element of a list together with its index, concatenating
   the results; [apply_with_idx] starts the indices at 0. *)
Fixpoint apply_with_idx' {A B} (f : nat -> A -> list B) (x : nat) (l : list A) : list B :=
  match l with
  | [] => []
  | a :: l => f x a ++ apply_with_idx' f (S x) l
  end.

Definition apply_with_idx {A B} (f : nat -> A -> list B) := apply_with_idx' f 0.
