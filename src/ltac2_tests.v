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
Abort.


(* My goal is to perform an induction, and to get all the inductions hypothesis *)

Ltac2 rec number_of_hypothesis_lt
(h1: (ident * constr option * constr) list) 
(h2 : (ident * constr option * constr) list) := 
match h1 with
| [] => match h2 with
        | [] => false
        | x :: xs => true
      end
| x :: xs => match h2 with
        | [] => false
        | y :: ys => number_of_hypothesis_lt xs ys
      end
end.

Ltac2 rec new_hypothesis
(h1: (ident * constr option * constr) list) 
(h2 : (ident * constr option * constr) list) := 
match h1 with
| [] => h2
| x :: xs => match h2 with
        | [] => []
        | y :: ys => new_hypothesis xs ys
      end
end.

Ltac2 bool_printer (b : bool) :=
match b with
| true => ltac1:(idtac "true")
| false => ltac1:(idtac "false")
end.

Ltac2 rec hyps_printer (h : (ident * constr option * constr) list) 
:=
match h with
| [] => ()
| x :: xs => match x with
            | (id, opt, cstr) => 
let () := Message.print (Message.concat (Message.of_ident id)
                                        (Message.concat (Message.of_string " : ")
                                                        (Message.of_constr cstr))) 
in hyps_printer xs
end 
end.

Ltac2 rec hyps_copy (h : (ident * constr option * constr) list) 
:=
match h with
| [] => ()
| x :: xs => match x with
            | (id, opt, cstr) => let () := copy id
in hyps_copy xs
end 
end.

Ltac2 hyps_minus_term (h : (ident * constr option * constr) list) (id : ident)
:= 
let t := Control.hyp id in
let () := Message.print (Message.of_constr t) in 
let rec aux h id := 
match h with
| [] => []
| x :: xs => match x with
      | (id', opt, cstr) => let t' := Control.hyp id' in if Constr.equal t' t then xs 
                           else x :: aux xs t
      end
end in aux h t.


Inductive foo : nat -> nat -> Prop :=
| bar2 : foo 0 0
| bar3 : forall n n', n = n' -> foo (S (S n)) n'
| bar1 : forall n n', foo n n' -> foo (S n) (S n').

Ltac2 Eval Std.induction.

Lemma test_induction n n' : foo n n' -> foo (S n) (S n').
Proof.
intros H. 
let h := hyps () in
let h' := hyps_minus_term h @H in
let () := hyps_printer h' in
induction H ;
Control.enter (fun () => (let h'' := hyps () in 
hyps_copy (new_hypothesis h' h''))).










