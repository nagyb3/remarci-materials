Require Import Setoid.

Parameter Ty     : Type.
Parameter Tm     : Ty -> Type.

Parameter arr        : Ty -> Ty -> Ty.
Notation "A ⇒ B"     := (arr A B) (at level 80, right associativity).
Parameter app        : forall {A B : Ty}, Tm(A ⇒ B) -> Tm A -> Tm B.
Notation "x ⋅ y"     := (app x y) (at level 50, left associativity).
Parameter lam        : forall {A B : Ty}, (Tm A -> Tm B) -> Tm (A ⇒ B).
Notation "'λ' x , f" := (lam (fun x => f)) (at level 81, x name).
Parameter arrβ       : forall {A B : Ty} (b : Tm A -> Tm B) (a : Tm A), lam b ⋅ a = b a.
Parameter arrη       : forall {A B : Ty} (f : Tm (A ⇒ B)), f = lam (fun a => f ⋅ a).

Parameter Prod   : Ty -> Ty -> Ty.
Notation "A × B" := (Prod A B) (at level 78, right associativity). (* \times *)
Parameter pair   : forall {A B}, Tm A -> Tm B -> Tm (A × B).
Notation "x , y" := (pair x y) (at level 80, right associativity).
Parameter fst    : forall {A B}, Tm (A × B) -> Tm A.
Parameter snd    : forall {A B}, Tm (A × B) -> Tm B.
Parameter Prodβ₁ : forall {A B} (a : Tm A) (b : Tm B), fst (a , b) = a.
Parameter Prodβ₂ : forall {A B} (a : Tm A) (b : Tm B), snd (a , b) = b.
Parameter Prodη  : forall {A B} (ab : Tm (A × B)), ab = (fst ab , snd ab).

Parameter Unit   : Ty.
Notation "⊤"     := Unit. (* \top *)
Parameter tt     : Tm ⊤.
Parameter Unitη  : forall (t : Tm ⊤), t = tt.

Parameter Sum   : Ty -> Ty -> Ty.
Notation "A ⊎ B" := (Sum A B) (at level 79, right associativity). (* \uplus *)

Parameter inl    : forall {A B}, Tm A -> Tm (A ⊎ B).
Parameter inr    : forall {A B}, Tm B -> Tm (A ⊎ B).
Parameter case   : forall {A B C}, Tm (A ⊎ B) -> (Tm A -> Tm C) -> (Tm B -> Tm C) -> Tm C.
Parameter Sumβ₁  : forall {A B C} (cl : Tm A -> Tm C) (cr : Tm B -> Tm C) (a : Tm A), case (inl a) cl cr = cl a.
Parameter Sumβ₂  : forall {A B C} (cl : Tm A -> Tm C) (cr : Tm B -> Tm C) (b : Tm B), case (inr b) cl cr = cr b.
Parameter Sumη   : forall {A B C} (c : Tm (A ⊎ B) -> Tm C) (w : Tm (A ⊎ B)), c w = case w (fun a => c (inl a)) (fun b => c (inr b)).

Parameter Empty   : Ty.
Notation "⊥"      := Empty. (* \bot *)
Parameter exfalso : forall {A : Ty}, Tm ⊥ -> Tm A.
Parameter Emptyη  : forall {A : Ty} (a : Tm ⊥ -> Tm A) (w : Tm ⊥), a w = exfalso w.

Parameter (Nat    : Ty).
Parameter (zero   : Tm Nat).
Parameter (suc    : Tm Nat -> Tm Nat).
Parameter (iteNat : forall {N}, Tm N -> (Tm N -> Tm N) -> Tm Nat -> Tm N).
Parameter (Natβ₁  : forall {N} {z : Tm N} {s},   iteNat z s zero = z).
Parameter (Natβ₂  : forall {N} {z : Tm N} {s u}, iteNat z s (suc u) = s (iteNat z s u)).
Definition plus (a b : Tm Nat) : Tm Nat := iteNat b suc a.
Arguments plus _ _ / : assert.

(*
   Inductive types:
   - defined by constructors
   - eliminated by iterators
   - beta rules simplify iterator applied to constructor

   Coinductive types:
   - defined by destructors
   - created by generators
   - beta rules simplify destructor applied to generator

         -------> C <------- 
        /         ^         \
       /          ¦          \
      /          case         \
     /            ¦            \
   A ---inl---> A ⊎ B <---inr--- B

         -------- C -------- 
        /         ¦         \
       /        pair'        \
      /           ¦           \
     L            v            J
   A <---fst--- A × B ---snd---> B

   pair' : (C -> A) -> (C -> B) -> C -> A × B
   pair  :       A  ->       B  ->      A × B
*)

Module StreamMeta.

  Import Datatypes.

  (* https://rocq-prover.org/doc/V8.20.0/refman/language/core/coinductive.html#caveat *)
  (* CoInductive Stream (A : Type) : Type := cons : A -> Stream A -> Stream A. *)

  CoInductive Stream (A : Type) : Type := cons {
    head : A;
    tail : Stream A;
  }.
  Arguments head {_} _.
  Arguments tail {_} _.

  (* termination vs progress *)
  CoFixpoint gen {C A} (h : C -> A) (t : C -> C) (c : C) : Stream A :=
    {| head := h c; tail := gen h t (t c) |}.

  (* 0, 1, 2, 3, ... *)
  Definition nats : Stream nat := gen id S 0.

  Compute head nats.
  Compute head (tail nats).
  Compute head (tail (tail nats)).
  Compute head (tail (tail (tail nats))).

  (* 1, 1, 1, 1, ... *)
  Definition const1  : Stream nat := gen id id 1.
  Definition const1' : Stream nat := gen (fun _ => 1) id tt.

  Compute head const1.
  Compute head (tail const1).
  Compute head (tail (tail const1)).
  Compute head (tail (tail (tail const1))).

  Compute head const1'.
  Compute head (tail const1').
  Compute head (tail (tail const1')).
  Compute head (tail (tail (tail const1'))).

  CoFixpoint const1_cfp : Stream nat := {|
    head := 1;
    tail := const1_cfp;
  |}.

  (* pointwise addition of two streams *)
  CoFixpoint addStream (s1 s2 : Stream nat) : Stream nat := {|
    head := head s1 + head s2;
    tail := addStream (tail s1) (tail s2);
  |}.

  Compute head (addStream nats const1).
  Compute head (tail (addStream nats const1)).
  Compute head (tail (tail (addStream nats const1))).

  Definition addStream' (s1 s2 : Stream nat) : Stream nat := 
    gen
    (fun x => head (fst x) + head (snd x))
    (fun x => pair (tail (fst x)) (tail (snd x)))
    (pair s1 s2).

  Compute head (addStream' nats const1).
  Compute head (tail (addStream' nats const1)).
  Compute head (tail (tail (addStream' nats const1))).

  Definition mapStream {A B} (f : A -> B) (s : Stream A) : Stream B. Admitted.

End StreamMeta.

Module Stream.

  Parameter Stream   : Ty -> Ty.
  Parameter head     : forall {A}, Tm (Stream A) -> Tm A.
  Parameter tail     : forall {A}, Tm (Stream A) -> Tm (Stream A).
  Parameter gen      :
    forall {A C}, (Tm C -> Tm A) -> (Tm C -> Tm C) -> Tm C -> Tm (Stream A).

  Parameter Streamβ₁ : forall {A C} (h : Tm C -> Tm A) (t : Tm C -> Tm C) (c : Tm C),
    head (gen h t c) = h c.
  Parameter Streamβ₂ : forall {A C} (h : Tm C -> Tm A) (t : Tm C -> Tm C) (c : Tm C),
    tail (gen h t c) = gen h t (t c).

  Definition nats : Tm (Stream Nat) := gen id suc zero.

  Lemma head_nats : head nats = zero.
  Proof. unfold nats. rewrite Streamβ₁. reflexivity. Qed.
  Lemma tail_head_nats : head (tail nats) = suc zero.
  Proof. unfold nats. rewrite Streamβ₂. rewrite Streamβ₁. reflexivity. Qed.
  Lemma tail_tail_head_nats : head (tail (tail nats)) = suc (suc zero).
  Proof. unfold nats. rewrite ! Streamβ₂. rewrite Streamβ₁. reflexivity. Qed.

  Definition const1  : Tm (Stream Nat) := gen id id (suc zero).
  (* Definition const1' : Tm (Stream Nat) := gen (fun _ => suc zero) id tt. *)

  Lemma head_const1 : head const1 = suc zero.
  Proof. unfold const1. rewrite Streamβ₁. reflexivity. Qed.
  Lemma tail_head_const1 : head (tail const1) = suc zero.
  Proof. unfold const1. rewrite Streamβ₂. rewrite Streamβ₁. reflexivity. Qed.
  Lemma tail_tail_head_const1 : head (tail (tail const1)) = suc zero.
  Proof. unfold const1. rewrite ! Streamβ₂. rewrite Streamβ₁. reflexivity. Qed.

(*
  Definition addStream  (s1 s2 : Tm (Stream Nat)): Tm (Stream Nat) :=
    gen
    (fun p => plus (head (fst p)) (head (snd p)))
    (fun p => (tail (fst p) , tail (snd p)))
    (s1 , s2).

  Goal head (addStream nats const1) = suc zero.
  Proof.
  Admitted.
  Goal head (tail (addStream nats const1)) = suc (suc zero).
  Proof.
  Admitted.
  Goal head (tail (tail (addStream nats nats))) = suc (suc (suc (suc zero))).
  Proof.
  Admitted.

  Definition mapStream {A B} (f : Tm A -> Tm B) (s : Tm (Stream A)) : Tm (Stream B). Admitted.
*)
End Stream.

Inductive SPos : (Ty -> Ty) -> Type :=
  | idP    : SPos (fun X => X)
  | constP : forall (A : Ty), SPos (fun _ => A)
  | ProdP  : forall {F G}, SPos F -> SPos G -> SPos (fun X => F X × G X)
  | SumP   : forall {F G}, SPos F -> SPos G -> SPos (fun X => F X ⊎ G X)
  | ArrP   : forall {F} (A : Ty), SPos F -> SPos (fun X => A ⇒ F X)
.

Fixpoint map {F : Ty -> Ty} {A B : Ty} (FP : SPos F) (f : Tm A -> Tm B) : Tm (F A) -> Tm (F B) :=
  match FP in SPos F return Tm (F A) -> Tm (F B) with
  | idP         => f
  | constP A    => id
  | ProdP FP GP => fun t => (map FP f (fst t), map GP f (snd t))
  | SumP  FP GP => fun t => case t (fun u => inl (map FP f u)) (fun v => inr (map GP f v))
  | ArrP   A FP => fun t => lam (fun x => map FP f (t ⋅ x))
  end.

Parameter Ind  : forall {F : Ty -> Ty}, SPos F -> Ty.
Parameter con  : forall {F : Ty -> Ty} (FP : SPos F), Tm (F (Ind FP)) -> Tm (Ind FP).
Parameter ite  : forall {F : Ty -> Ty} (FP : SPos F) {C : Ty}, (Tm (F C) -> Tm C) -> Tm (Ind FP) -> Tm C.
Parameter Indβ : forall {F : Ty -> Ty} (FP : SPos F) {C : Ty} (f : Tm (F C) -> Tm C) (w : Tm (F (Ind FP))),
  ite FP f (con FP w) = f (map FP (ite FP f) w).
Parameter Indη : forall {F : Ty -> Ty} (FP : SPos F) {C : Ty} (f : Tm (F C) -> Tm C)
  (z : Tm (Ind FP) -> Tm C),
  (forall (w : Tm (F (Ind FP))), z (con FP w) = f (map FP z w)) ->
  z = ite FP f.

(* greatest fixpoint *)
Parameter Coind  : forall {F : Ty -> Ty}, SPos F -> Ty.
Parameter des    : forall {F : Ty -> Ty} (FP : SPos F), Tm (Coind FP) -> Tm (F (Coind FP)).
Parameter gen    : forall {F : Ty -> Ty} (FP : SPos F) {C : Ty}, (Tm C -> Tm (F C)) -> Tm C -> Tm (Coind FP).
Parameter Coindβ : forall {F : Ty -> Ty} (FP : SPos F) {C : Ty} (f : Tm C -> Tm (F C)) (c : Tm C),
  des FP (gen FP f c) = map FP (gen FP f) (f c).
Parameter Coindη : forall {F : Ty -> Ty} (FP : SPos F) {C : Ty} (f : Tm C -> Tm (F C))
  (z : Tm C -> Tm (Coind FP)), (forall (c : Tm C), des FP (z c) = map FP z (f c)) -> z = gen FP f.

Module StreamCoind.

  (* define Stream using Coind *)
  Definition StreamF (A : Ty) : Ty -> Ty := fun X => A × X.
  Lemma StreamP A : SPos (StreamF A).  
  Proof.
    unfold StreamF.
    apply ProdP.
    apply constP.
    apply idP.
  Defined.

  Definition Stream (A : Ty) := Coind (StreamP A).
  Definition head {A} (s : Tm (Stream A)) : Tm A := fst(des _ s).
  Definition tail {A} (s : Tm (Stream A)) : Tm (Stream A) := snd (des _ s).
  Definition genStream {A C} (h : Tm C -> Tm A) (t : Tm C -> Tm C) (c : Tm C) : Tm (Stream A) := gen _ (fun x => h x, t x) c .

  Lemma Streamβ₁ : forall {A C} (h : Tm C -> Tm A) (t : Tm C -> Tm C) (c : Tm C),
  head (genStream h t c) = h c.
  Proof.
    intros.
    cbv.
    rewrite Coindβ.
    cbv.
    rewrite ! Prodβ₁.
  Defined.

  Lemma Streamβ₂ : forall {A C} (h : Tm C -> Tm A) (t : Tm C -> Tm C) (c : Tm C),
  tail (genStream h t c) = genStream h t (t c).
  Proof.
    intros.
    cbv.
    rewrite Coindβ.
    cbv.
    rewrite ! Prodβ₂.
  Defined.

End StreamCoind.

Module AddMachine.

  (* define adding machines: we can input a number, we can get a number as an output, and we can press a button *)
  Definition AddF : Ty -> Ty := fun X => (Nat => X) × Nat × X.
  Lemma AddP : SPos AddF.
  Proof.
    repeat constructor.
  Defined.

  Definition Add := Coind AddP.

  (* the internal state of this machine should be a natural numbers, it
     (1) adds all the numbers in its input to its internal state, and
     (2) outputs its internal state if asked, and
     (3) makes the internal state zero, if the button is pressed
   *)
  Definition addMachine : Tm Add := gen _ (fun x => (λ y, plus x y), x, zero) zero.
  Definition addMachineN (n : Tm Nat) : Tm Add. Admitted.

  Definition add (x : Tm Nat) (m : Tm Add) : Tm Add := fst (des _ m) ⋅ x.
  Definition output (m : Tm Add) : Tm Nat := fst (snd (des _ m)).
  Definition reset (m : Tm Add) : Tm Add := snd (snd (des _ m)).
  (* do some interaction with the machine *)

  Goal
  output (add (suc zero) (add (suc zero) addMachine)) = suc (suc zero).
  Proof.
  Admitted.

  Goal
  output (reset (add (suc zero) (add (suc zero) addMachine))) = zero.
  Proof.
  Admitted.

  Goal
  output (reset (add (suc zero) (add (suc zero) (addMachineN (suc zero))))) = suc zero.
  Proof.
  Admitted.

  (* Why are there no β rules? *)
  (* How could this machine be generalized? *)
  (*
     +-+-+-+-----+  ┌─┬─┬─┬─────┐
     |1|2|3|.....|  │1│2│3│.....│
     +-+-+-+.234.|  ├─┼─┼─┤.234.│
     |4|5|6|.....|  │4│5│6│.....│
     +-+-+-+-----+  ├─┼─┼─┼─────┤
     |7|8|9| Out |  │7│8│9│ Out │
     +-+-+-+-----+  ├─┼─┴─┼─────┤
     |0|Add|Reset|  │0│Add│Reset│
     +-----+-----+  └─┴───┴─────┘
  *)

  Definition genAddMachine {C}
    (addBtn : Tm C -> Tm Nat -> Tm C)
    (outBtn : Tm C -> Tm Nat)
    (resetBtn : Tm C -> Tm C)
    (c : Tm C) : Tm Add. Admitted.

  Parameters (max : Tm Nat -> Tm Nat -> Tm Nat)
             (maxZero : forall n, max zero n = n).

  Definition maxMachine : Tm Add := genAddMachine max id (fun _ => zero) zero.

  Lemma Addβ₁ C a o r (c : Tm C) n : add n (genAddMachine a o r c) = genAddMachine a o r (a c n).
  Proof.
  Admitted.

  Lemma Addβ₂ C a o r (c : Tm C) : output (genAddMachine a o r c) = o c.
  Proof.
  Admitted.

  Lemma Addβ₃ C a o r (c : Tm C) : reset (genAddMachine a o r c) = genAddMachine a o r (r c).
  Proof.
  Admitted.

  Goal forall n m, output (add m (add n maxMachine)) = max n m.
  Proof.
  Admitted.

End AddMachine.

(*
   We have a machine with some internal state and functions which either
   present something based on this state, or modify the state of the
   machine. Does this seem familiar?

   What if I presented the machine like this? (Assignment is an expression
   for simplicity.)

   Add {
     state : Nat;

     add (this : Add, n : Nat) : Add {
       return this.state += n;
     }

     output (this : Add) : Nat {
       return this.state;
     }

     reset (this : Add) : Add {
       return this.state = 0;
     }
   }

   What is the abstraction of this?
*)

Module ChocMachine.

  (* define chocolate machines *)
  (* Try to figure out the type operator yourself as well. The answer is at
     the end of the file, so you can continue. *)
  Definition FChoc : Ty -> Ty. Admitted.
  Definition ChocP : SPos FChoc. Admitted.
  Definition chocMachine : Tm (Coind ChocP). Admitted.
  (* a concrete machine where the internal state is the number of
     chocolates and the amount of money in the machine (a pair of Nats),
     (1) we can add in money,
     (2) we can check the money inside,
     (3) we can try to get a chocholate (if there is more than one chocolate in the machine
     and there is enough money, this descreases the number of chocolates by
     1, and decreases the money by the price of the chocolate (say, 10)),
     (4) we can get back the money which is inside (this just zeroes the current money)
   *)

End ChocMachine.

Module Misc.

  Record Iso (A B : Ty) := mkIso {
    f : Tm A -> Tm B ;
    g : Tm B -> Tm A ;
    gf : forall a, g (f a) = a ;
    fg : forall b, f (g b) = b
  }.
  Notation "A ≅ B" := (Iso A B) (at level 80). (* \cong *)

  (* Ind over constants *)
  Goal forall (C : Ty), Ind (constP C) ≅ C.
  Proof.
  Admitted.

  (* Coind over constants *)
  Goal forall (C : Ty), Coind (constP C) ≅ C.
  Proof.
  Admitted.

  (* fixpoints *)
  Goal forall (F : Ty -> Ty) (FP : SPos F) (A : Ty), F (Ind FP) ≅ Ind FP.
  Proof.
  Admitted.

  Goal forall (F : Ty -> Ty) (FP : SPos F) (A : Ty), F (Coind FP) ≅ Coind FP.
  Proof.
  Admitted.

  (* Cantor's argument / diagonalization *)
  (* Goal (Nat ⇒ Bool) ≅ Nat -> true = false. *)
  (* Proof. *)
  (* Admitted. *)

  (* products as inductive types *)
  Definition ProdF (A B : Ty) (X : Ty) : Ty := A ⇒ B ⇒ X.
  Definition ProdI (A B : Ty) : Ty := @Ind (ProdF A B) ltac:(repeat constructor).

  (* define comma, fst and snd and show beta and eta *)

  Goal forall A B, A × B ≅ ProdI A B.
  Proof.
  Admitted.

End Misc.

(* Definition FChoc : Ty -> Ty := fun X => (Nat ⇒ X) × Nat × (⊤ ⊎ X) × X. *)
