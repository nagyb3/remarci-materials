(**
  Type systems (Nyelvek típusrendszere) tutorial (gyakorlat)

  Website of the course: https://bitbucket.org/akaposi/sogateotvos
  Available also from the website of the lecturer: https://akaposi.web.elte.hu

  Requirements:
  - In person attendance at tutorials (you can miss 3)
  - You have to go to the tutorial that you are registered to in Neptun
  - At the beginning of each tutorial a mini-exam with Coq programming exercises,
    there will be at least 10 of these
  - Point limits are on the website of the course

  More info:
  - Teams group: "Nyelvek tipusrendszere 2025 osz", code: zobxux0 -- this is where you
    should ask questions about the material
  - We will use Rocq (Coq) at the tutorials: https://coq.inria.fr
    - Recommended development environment: CoqIDE, Emacs, VSCode (VSCoq)
      use Windows on the lab computers: C:\Coq-Platform~8.20~2025.01/bin/coqide.exe
    - CoqIDE allows LaTeX input for Unicode symbols:
        \latexparancs + shift + space
        \cdot + shift + space = ⋅
*)

(*
  Who have used Coq before?

  What is a programming language?
*)

Require Import Nat String List.
Import ListNotations.

Open Scope string_scope.

(** We will study a small expression language, we will understand
typability, type erasure type inference.

The language is called Razor, it contains boolean and natural number
expressions. Example program:

if isZero (num 0 + num 1) then false else isZero (num 0)

This program evaluates (runs) in the following steps:

if isZero (num 0 + num 1) then false else isZero (num 0) ~~~~>
if isZero (        num 1) then false else isZero (num 0) ~~~~>
if false                  then false else isZero (num 0) ~~~~>
                                          isZero (num 0) ~~~~>
                                          true
  *)

(************************************************************
 abstraction level 1: a program is a string
*************************************************************

"num 3 - num 2" does not make sense because we don't have subtraction

"isZero (num 1)"   ≠   "isZero     (num 1)"


 *)



Goal "isZero (num 1)" <> "isZero     (num 1)".
Proof.
  discriminate.
Qed.

(************************************************************
 abstraction level 2: a program is a list of lexical elements
*************************************************************

Lexical elements: (, ), true, false, if, then, else, num, isZero, +, 0, 1, 2, ...

Now both "isZero (num 1)" and "isZero     (num 1)" are the same lists [isZero, (, num, 1, )].

But: [(, true] does not make sense (closing bracket is missing).

[(, true, )]  ≠  [true]

 *)

Module L.

Inductive Lex : Type := Open | Close | true | false | if' | then' | else' | num (n : nat) | isZero | plus.

Goal [Open; true; Close] <> [true].
Proof.
  discriminate.
Qed.

(* you can fix this *)
Definition to_string (n : nat) : string := "NUM".

(* a very stupid printing function *)
Fixpoint print (ls : list Lex) : string :=
  match ls with
  | nil => ""
  | Open   :: ls => "( " ++ print ls
  | Close  :: ls => ") " ++ print ls
  | true   :: ls => "true " ++ print ls
  | false  :: ls => "false " ++ print ls
  | if'    :: ls => "if " ++ print ls
  | then'  :: ls => "then " ++ print ls
  | else'  :: ls => "else " ++ print ls
  | num n  :: ls => "num " ++ to_string n ++ " " ++ print ls
  | isZero :: ls => "isZero " ++ print ls
  | plus   :: ls => "+ " ++ print ls
  end.

Compute (print [Open; true; Close]).
Compute (print [if'; Open; isZero; num 5; Close; then'; num 0; else'; Open; num 1; plus; num 2; Close]).

(* homework: write a lexer *)

End L.

(************************************************************
 abstraction level 3: a program is an abstract syntax tree
*************************************************************)

Module U.

(* these are the programs: *)
Inductive Tm : Type :=
  | true   : Tm
  | false  : Tm
  | ite    : Tm -> Tm -> Tm -> Tm
  | num    : nat -> Tm
  | isZero : Tm -> Tm
  | plus   : Tm -> Tm -> Tm
.

Fail Definition wrong : Tm := ite true (num 0).
Definition notMeaningful : Tm := isZero true.

(*
we can only define a C-style evaluator (meaning, denotational semantics, interpreter)
of the AST where booleans and integers are merged
 *)

(* EX: finish this *)
Fixpoint eval (t : Tm) : nat :=
  match t with
  | true => 1
  | false => 0
  | ite t u v => match (eval t) with
                 | 0 => eval v
                 | _ => eval u
                 end
  | num n => n
  | isZero t => if eval t then 1 else 0
(*   | isZero t => match (eval t) with
                | 0 => 1
                | _ => 0
                * end
*)
 | plus t u => eval t + eval u
  end.

(* EXE *)
Example notEq : exists t1 t2 : Tm, t1 <> t2 /\ eval t1 = eval t2.
Proof.
  exists true, (ite true true true).
  split.
  * discriminate.
  * simpl. reflexivity.
Qed.

(* EXE *)
Fixpoint toLex (t : Tm) : list L.Lex :=
  match t with
  | true => [L.true]
  | false => [L.false]
  | ite t u v => L.if' :: toLex t ++ L.then' :: toLex u ++ L.else' :: toLex v (* maybe we need some brackets here? *)
  | num n => [L.num n]  
  | isZero t => L.isZero :: toLex t
  | plus t u => toLex t ++ L.plus :: toLex u
  end.

(* homework: write a parser, show its correctness: parse ∘ toLex = id *)

End U.

(************************************************************
 abstraction level 4: a program is a well-typed syntax tree
*************************************************************)

Module Typed.

Inductive Ty : Type := Bool | Nat.

Inductive Tm : Ty -> Type :=
  | true   : Tm Bool
  | false  : Tm Bool
  | ite    : forall {A : Ty}, Tm Bool -> Tm A -> Tm A -> Tm A
  | num    : nat -> Tm Nat
  | isZero : Tm Nat -> Tm Bool
  | plus   : Tm Nat -> Tm Nat -> Tm Nat
.

Notation "x + y" := (plus x y) (at level 50, left associativity).

(* ite has an implicit argument: *)
Check ite true (num 1) (num 2).
Fail Check ite true (num 1) (nunm 2).
Check @ite Nat true (num 1) (num 2).
Check @ite _ true (num 1) (num 1).
Fail Check @ite Bool true (num 1) (num 2).
Fail Check ite true (num 1) false.

(**
  Type erasure: from typed to untyped
*)
Reserved Notation "⟦ a ⟧".
Fixpoint erase {A : Ty} (a : Tm A) : U.Tm :=
  match a with
  | true => U.true
  | false => U.false
  | ite t u v => U.ite ⟦ t ⟧ ⟦ u ⟧ ⟦ v ⟧
  | num n => U.num n
  | isZero t => U.isZero ⟦ t ⟧
  | plus u v => (U.plus ⟦ u ⟧ ⟦ v ⟧)
  end
where "⟦ a ⟧" := (erase a).
(*
  \lobrk = ⟦
  \robrk = ⟧
*)

(* EXE *)
Goal exists (A : Ty) (a : Tm A), ⟦ a ⟧ = U.isZero (U.num 2).
Proof.
  exists Bool, (isZero (num 2)).
  simpl. reflexivity.
Qed.

(* EXE *)
Goal exists (A : Ty) (a : Tm A), ⟦ a ⟧ = U.ite (U.isZero (U.plus (U.num 0) (U.num 1))) U.false (U.isZero (U.num 0)).
Proof.
  eexists.
  exists (ite (isZero (plus (num 0) (num 1))) false (isZero (num 0))).
  simpl. reflexivity.
Qed.

(* EXE *)
Goal exists (A : Ty) (a : Tm A), ⟦ a ⟧ = U.ite U.true U.true U.true.
Proof.
Admitted.

(**
  Think about it: is there an untyped expression which cannot be the result of type erasure?

  Examples:

  U.ite U.true (U.num 1) U.false
  U.ite (U.num 1) U.true U.true
  U.isZero U.true
*)

(* HARD *)
Goal ~ exists (A : Ty) (a : Tm A), ⟦ a ⟧ = U.isZero (U.true).
Proof.
  Locate "~". Print not.
  (* unfold not *)
  unfold "~".
  intros.
  destruct H.
  destruct H.
  destruct x0.
  simpl in H. discriminate.
  simpl in H. discriminate.
  simpl in H. discriminate.
  simpl in H. discriminate.
  simpl in H.
  remember Nat.
  destruct x0.
  discriminate.
  discriminate.
  simpl in H. discriminate.
  simpl in H. discriminate.
  discriminate.
  simpl in H. discriminate.
  simpl in H. discriminate.
Qed.

(* A : Ty & Tm A   <-  pair of a type and a term of that type, constructor: existT _ _ *)
Locate "&".
Print sigT.

Definition vector (n : nat) := { l : list nat & List.length l = n }.
Example vec : vector 5.
Proof.
  exists [1; 2; 3; 4; 5].
  simpl. reflexivity.
Defined.

Example vec' : vector 5 := existT _ [1; 2; 3; 4; 5] eq_refl.

Goal vec = vec'.
Proof. reflexivity. Qed.

Example p : nat * nat.
Proof.
  split.
  exact 3.
  exact 5.
Defined.

Example p' : nat * nat := pair 3 5.

Goal p = p'.
Proof. reflexivity. Qed.

(**
  Type inference
  EXE: finish it! *)
Fixpoint infer (a : U.Tm) : option {A : Ty & Tm A} :=
  match a with
  | U.true  => Some (existT _ Bool true)
  | U.false => Some (existT _ Bool false)
  | U.ite t u v =>
    match infer t, infer u, infer v with
    | Some (existT _ Bool t'),
      Some (existT _ Nat  u'),
      Some (existT _ Nat  v') =>
        Some (existT _ Nat (ite t' u' v'))
    | Some (existT _ Bool t'),
      Some (existT _ Bool u'),
      Some (existT _ Bool v') =>
        Some (existT _ Bool (ite t' u' v'))
    | _, _, _ => None
    end
  | _ => None
  end.

(* EXE *)
Goal infer (U.plus U.true (U.num 1)) = None.
Proof.
Admitted.

(* EXE *)
Goal infer (U.ite U.true (U.num 1) U.false) = None.
Proof.
Admitted.

(* EXE *)
Goal ~ infer (U.plus (U.num 0) (U.num 1)) = Some (existT _ Nat (num 1)).
Proof.
Admitted.

(* EXE *)
Goal infer (U.plus (U.num 0) (U.num 1)) = Some (existT _ Nat (num 0 + num 1)).
Proof.
Admitted.

(* EXE - correctness of infer *)
Lemma correctInfer (A : Ty) (a : Tm A) : infer ⟦ a ⟧ = Some (existT _ A a).
Proof.
Admitted.

(* homework: harder *)
Lemma inferCorrect (t : U.Tm) (A : Ty) (a : Tm A) :
   infer t = Some (existT _ A a) -> ⟦ a ⟧ = t.
Proof.
Admitted.

(* EXE: same as above, but use the properties of infer *)
Definition t : U.Tm := U.ite (U.isZero (U.plus (U.num 0) (U.num 1))) U.false (U.isZero (U.num 0)).
Goal exists (A : Ty) (a : Tm A), ⟦ a ⟧ = t.
Proof.
Admitted.

(* EXE: harder: do destruct on a, easier: use correctInfer *)
Goal ~ exists (A : Ty) (a : Tm A), ⟦ a ⟧ = U.ite U.true U.true (U.num 0).
Proof.
Admitted.

(* EXE *)
Goal ~ exists (A : Ty) (a : Tm A), ⟦ a ⟧ = U.ite (U.num 0) (U.num 1) (U.num 0).
Proof.
Admitted.

(* EXE *)
Goal ~ exists (A : Ty) (a : Tm A), ⟦ a ⟧ = (U.plus U.true (U.num 1)).
Proof.
Admitted.

(* EXE *)
Goal ~ exists (A : Ty) (a : Tm A), ⟦ a ⟧ = (U.plus (U.isZero (U.num 1)) (U.num 1)).
Proof.
Admitted.

(* EXE *)
Goal ~ exists (A : Ty) (a : Tm A), ⟦ a ⟧ = U.ite U.true U.false (U.num 1).
Proof.
Admitted.

Definition evalTy (A : Ty) : Type := match A with
                                     | Nat => nat
                                     | Bool => bool
                                     end.

(* EXE: write a type-correct evaluator *)
Fixpoint evalTm (A : Ty) (t : Tm A) : evalTy A. Admitted.
    
(* EXE *)
Example notEq : exists A : Ty, exists t1 t2 : Tm A, ~ t1 = t2 /\ evalTm A t1 = evalTm A t2.
Proof.
Admitted.
    
End Typed.

Module EquationalTheory.
(**
  Now Razor is a GAT, we even know its equational theory (how to run programs, which programs should be equal).
*)

Parameter (Ty   : Type).
Parameter (Bool : Ty).
Parameter (Nat  : Ty).

Parameter (Tm     : Ty -> Type).
Parameter (true   : Tm Bool).
Parameter (false  : Tm Bool).
Parameter (ite    : forall {A : Ty}, Tm Bool -> Tm A -> Tm A -> Tm A).
Parameter (num    : nat -> Tm Nat).
Parameter (isZero : Tm Nat -> Tm Bool).
Parameter (plus   : Tm Nat -> Tm Nat -> Tm Nat).
Notation "x + y" := (plus x y) (at level 50, left associativity).

(* semantical equations *)
Parameter (iteβ₁    : forall {A} {u v : Tm A}, ite true u v = u).
Parameter (iteβ₂    : forall {A} {u v : Tm A}, ite false u v = v).
Parameter (isZeroβ₁ : isZero (num 0) = true).
Parameter (isZeroβ₂ : forall {n}, isZero (num (1 + n)) = false).
Parameter (plusβ    : forall {m n}, plus (num m) (num n) = num (m + n)).
(*
  \beta = β
  \_1 = ₁
  \_2 = ₂
*)

(* EXE *)
Goal ite (isZero (num 0 + num 1)) false (isZero (num 0)) = true.
Proof.
Admitted.

(* EXE *)
Goal exists n, ite (isZero (num 0 + num 0)) (num 10) (num 20) = num n.
Proof.
Admitted.

(* EXE *)
Goal forall n t, ite (isZero (num 0 + num 0)) (num 0 + num n) t = num n.
Proof.
Admitted.

(* EXE *)
Goal true = false -> forall (A : Ty) (a a' : Tm A), a = a'.
Proof.
Admitted.

(* EXE *)
Goal num 0 = num 1 -> forall (A : Ty) (a a' : Tm A), a = a'.
Proof.
Admitted.

(* EXE: can we prove this?
   If yes, prove it!
   If not, how do we change the language so that it can be proven? *)
Goal num 1 = num 2 -> forall (A : Ty) (a a' : Tm A), a = a'.
Proof.
Admitted.

End EquationalTheory.

(* EXE: extend the language with a <= operator, and do all the exercises above!
   EXE: extend the language with a - operator, and do all the exercises above!
   EXE: create example derivations with the new language!
 *)
