(** Experimenting with Ltac2 **) 

From Ltac2 Require Import Ltac2.

Import Ltac2.Control.


Ltac2 solve_and () :=
match! goal with
| [ |- ?e /\ ?f ] => let x := constr:(conj) in apply $x
end.

Ltac2 copy (h: ident) :=
  let h' := Control.hyp h in pose $h'.


Goal True -> True/\True. intros.
solve_and (). copy @H.
Abort.

Ltac2 copy_all_hypothesis () :=
let h := hyps () in
let rec copy_hyps l :=
  match l with
  | [] => ()
  | p :: l' => match p with
        | (id, _ , _) => let () := copy id in copy_hyps l' end
end in copy_hyps h.

(* /!\ Ltac2 doesn't allow uppercase variables *) 

Goal True -> False -> forall (A : Type), A = A -> True/\True.
intros.
copy_all_hypothesis ().
Abort.

Print Ltac2 Std.specialize.

Ltac2 specialize_and_return_hyp (h: constr) (ist : constr) (id: ident) :=
let () :=
Std.specialize (constr:($h $ist), Std.NoBindings) (Some (Std.IntroNaming ((Std.IntroIdentifier (@id)))))
in id.

(* Ltac2 tactic : instantiates an hypothesis recursively *)

Goal (forall (A : Type), A = A) -> False.
intros.
let id := specialize_and_return_hyp constr:(H) constr:(nat) @id in copy id.









