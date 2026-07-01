Require Import Setoid FunctionalExtensionality.

Parameter Ty : Type.
Parameter Tm : Ty -> Type.

Parameter arr        :  Ty -> Ty -> Ty.
Notation "A ⇒ B"     := (arr A B) (at level 80, right associativity).
Parameter app        :  forall {A B : Ty}, Tm(A ⇒ B) -> Tm A -> Tm B.
Notation "x ⋅ y"     := (app x y) (at level 50, left associativity).
Parameter lam        :  forall {A B : Ty}, (Tm A -> Tm B) -> Tm (A ⇒ B).
Notation "'λ' x , f" := (lam (fun x => f)) (at level 81, x name).
Parameter arrβ       :  forall {A B : Ty} (b : Tm A -> Tm B) (a : Tm A), lam b ⋅ a = b a.
Parameter arrη       :  forall {A B : Ty} (f : Tm (A ⇒ B)), f = lam (fun a => f ⋅ a).

Parameter Prod   :  Ty -> Ty -> Ty.
Notation "A × B" := (Prod A B) (at level 78, right associativity). (* \times *)
Parameter pair   :  forall {A B}, Tm A -> Tm B -> Tm (A × B).
Notation "x , y" := (pair x y) (at level 80, right associativity).
Parameter fst    :  forall {A B}, Tm (A × B) -> Tm A.
Parameter snd    :  forall {A B}, Tm (A × B) -> Tm B.
Parameter Prodβ₁ :  forall {A B} (a : Tm A) (b : Tm B), fst (a , b) = a.
Parameter Prodβ₂ :  forall {A B} (a : Tm A) (b : Tm B), snd (a , b) = b.
Parameter Prodη  :  forall {A B} (ab : Tm (A × B)), ab = (fst ab , snd ab).

Parameter Unit  :  Ty.
Notation "⊤"    := Unit. (* \top *)
Parameter tt    :  Tm ⊤.
Parameter Unitη :  forall (t : Tm ⊤), t = tt.

Parameter Sum    :  Ty -> Ty -> Ty.
Notation "A ⊎ B" := (Sum A B) (at level 79, right associativity). (* \uplus *)
Parameter inl    :  forall {A B}, Tm A -> Tm (A ⊎ B).
Parameter inr    :  forall {A B}, Tm B -> Tm (A ⊎ B).
Parameter case   :  forall {A B C}, Tm (A ⊎ B) -> (Tm A -> Tm C) -> (Tm B -> Tm C) -> Tm C.
Parameter Sumβ₁  :  forall {A B C} (cl : Tm A -> Tm C) (cr : Tm B -> Tm C) (a : Tm A), case (inl a) cl cr = cl a.
Parameter Sumβ₂  :  forall {A B C} (cl : Tm A -> Tm C) (cr : Tm B -> Tm C) (b : Tm B), case (inr b) cl cr = cr b.
Parameter Sumη   :  forall {A B C} (c : Tm (A ⊎ B) -> Tm C) (w : Tm (A ⊎ B)), c w = case w (fun a => c (inl a)) (fun b => c (inr b)).

Parameter Empty   :  Ty.
Notation "⊥"      := Empty. (* \bot *)
Parameter exfalso :  forall {A : Ty}, Tm ⊥ -> Tm A.
Parameter Emptyη  :  forall {A : Ty} (a : Tm ⊥ -> Tm A) (w : Tm ⊥), a w = exfalso w.

Module PosNeg.

  Inductive Pos : (Ty -> Ty) -> Type :=
    | idPos    : Pos (fun X => X)
    | constPos : forall (C : Ty), Pos (fun _ => C)
    | SumPos   : forall F G, Pos F -> Pos G -> Pos (fun X => F X ⊎ G X)
    | ProdPos  : forall F G, Pos F -> Pos G -> Pos (fun X => F X × G X)
    | ArrPos   : forall F G, Neg F -> Pos G -> Pos (fun X => F X ⇒ G X)
  with Neg : (Ty -> Ty) -> Type :=
    | constNeg : forall (C : Ty), Neg (fun _ => C)
    | SumNeg   : forall F G, Neg F -> Neg G -> Neg (fun X => F X ⊎ G X)
    | ProdNeg  : forall F G, Neg F -> Neg G -> Neg (fun X => F X × G X)
    | ArrNeg   : forall F G, Pos F -> Neg G -> Neg (fun X => F X ⇒ G X)
  .

  Scheme Pos_correct := Induction for Pos Sort Type with Neg_correct := Induction for Neg Sort Type.

  Fixpoint mapP {F : Ty -> Ty} {A B : Ty} (PosF : Pos F) (f : Tm A -> Tm B) : Tm (F A) -> Tm (F B) :=
    match PosF in Pos F return Tm (F A) -> Tm (F B) with
    | idPos                 => f
    | constPos C            => fun c => c
    | SumPos  F G PosF PosG => fun w => case w (fun u => inl (mapP PosF f u)) (fun v => inr (mapP PosG f v))
    | ProdPos F G PosF PosG => fun w => mapP PosF f (fst w), mapP PosG f (snd w)
    | ArrPos  F G NegF PosG => fun g => lam (fun x => mapP PosG f (g ⋅ (mapN NegF f x)))
    end
  with mapN {F : Ty -> Ty} {A B : Ty} (NegF : Neg F) (f : Tm A -> Tm B) : Tm (F B) -> Tm (F A) :=
    match NegF in Neg F return Tm (F B) -> Tm (F A) with
    | constNeg C            => fun c => c
    | SumNeg  F G NegF NegG => fun w => case w (fun u => inl (mapN NegF f u)) (fun v => inr (mapN NegG f v))
    | ProdNeg F G NegF NegG => fun w => mapN NegF f (fst w), mapN NegG f (snd w)
    | ArrNeg  F G PosF NegG => fun g => lam (fun x => mapN NegG f (g ⋅ (mapP PosF f x)))
    end.

  Goal forall F (PosF : Pos F) A (u : Tm (F A)), mapP PosF (fun x => x) u = u.
  Proof.
    induction PosF using Pos_correct with (P0 := fun F (NegF : Neg F) => forall A (u : Tm (F A)), mapN NegF (fun x => x) u = u) ; intros ; simpl.
    * reflexivity.
    * reflexivity.
    * rewrite (Sumη (fun x => x) u) at 2. f_equal ; extensionality x. now rewrite IHPosF1. now rewrite IHPosF2.
    * now rewrite IHPosF1, IHPosF2, Prodη.
    * rewrite arrη. f_equal ; extensionality x. rewrite IHPosF. f_equal. Check Pos_rect. now rewrite IHPosF0.
    * reflexivity.
  Admitted.

  Goal forall F (PosF : Pos F) A B C (w : Tm (F A)) (f : Tm B -> Tm C) (g : Tm A -> Tm B), mapP PosF (fun x => f (g x)) w = mapP PosF f (mapP PosF g w).
  Proof.
  Admitted.

  Goal forall F (NegF : Neg F) A (u : Tm (F A)), mapN NegF (fun x => x) u = u.
  Proof.
  Admitted.

  Goal forall F (NegF : Neg F) A B C (w : Tm (F A)) (f : Tm B -> Tm A) (g : Tm C -> Tm B), mapN NegF (fun x => f (g x)) w = mapN NegF g (mapN NegF f w).
  Proof.
  Admitted.

End PosNeg.

Module ExampleInds.

  (* remember natural numbers *)
  Parameter (Nat     : Ty).
  Parameter (zero    : Tm Nat).
  Parameter (suc     : Tm Nat -> Tm Nat).
  Parameter (iteNat  : forall {N}, Tm N -> (Tm N -> Tm N) -> Tm Nat -> Tm N).
  Parameter (Natβ₁   : forall {N} {z : Tm N} {s},   iteNat z s zero = z).
  Parameter (Natβ₂   : forall {N} {z : Tm N} {s u}, iteNat z s (suc u) = s (iteNat z s u)).

  Definition plus (a b : Tm Nat) : Tm Nat := iteNat b suc a.
  Arguments plus _ _ / : assert.

  Definition one   : Tm Nat := suc zero.
  Definition two   : Tm Nat := suc one.
  Definition three : Tm Nat := suc two.
  Definition four  : Tm Nat := suc three.
  Definition seven : Tm Nat := suc (suc (suc four)).

  Goal plus (suc zero) (suc (suc zero)) = suc (suc (suc zero)).
  Proof.
    unfold plus. rewrite Natβ₂. rewrite Natβ₁. reflexivity.
  Qed.

  (* we extend the language with binary trees *)
  Parameter (Tree    : Ty).
  Parameter (leaf    : Tm Tree).
  Parameter (node    : Tm Tree -> Tm Tree -> Tm Tree).
  Parameter (iteTree : forall {T}, Tm T -> (Tm T -> Tm T -> Tm T) -> Tm Tree -> Tm T).
  Parameter (Treeβ₁  : forall {T} {l : Tm T} {n}, iteTree l n leaf = l).
  Parameter (Treeβ₂  : forall {T} {l : Tm T} {n u v},
    iteTree l n (node u v) = n (iteTree l n u) (iteTree l n v)).

  Definition leaves : Tm Tree -> Tm Nat := iteTree one plus.
  Arguments leaves _ / : assert.

  Goal leaves (node (node leaf leaf) (node leaf leaf)) = four.
  Proof.
    simpl.
    rewrite ! Treeβ₂.
    rewrite ! Treeβ₁.
    cbv.
    rewrite ! Natβ₂.
    rewrite ! Natβ₁.
    rewrite ! Natβ₂.
    rewrite ! Natβ₁.
    reflexivity.
  Qed.

  Definition leaves' (t : Tm Tree) : Tm Nat :=
    suc (iteTree zero (fun t1 t2 => suc (plus t1 t2)) t).
  Arguments leaves' _ / : assert.

  Goal leaves' (node (node leaf leaf) (node leaf leaf)) = four.
  Proof.
    simpl.
    rewrite ! Treeβ₂.
    rewrite ! Treeβ₁.
    rewrite ! Natβ₂.
    rewrite ! Natβ₁.
    cbv.
    reflexivity.
  Qed.

  Goal leaves leaf = leaves' leaf.
  Proof.
  Admitted.

  Goal leaves (node leaf leaf) = leaves' (node leaf leaf).
  Proof.
  Admitted.

  Definition aTree := node (node leaf leaf) (node (node leaf leaf) leaf).
  Goal leaves aTree = leaves' aTree.
  Proof.
  Admitted.

  (* trees in the metatheory *)
  Inductive TreeM :=
    | leafM : TreeM
    | nodeM : TreeM -> TreeM -> TreeM.

  Fixpoint quoteTree (t : TreeM) : Tm Tree :=
    match t with
    | leafM => leaf
    | nodeM t1 t2 => node (quoteTree t1) (quoteTree t2)
    end.

  Fixpoint quoteNat (n : nat) : Tm Nat := match n with
                                          | O => zero
                                          | S n => suc (quoteNat n)
                                          end.

  Lemma quotePlus : forall m n,
    quoteNat (m + n) = plus (quoteNat m) (quoteNat n).
  Proof.
    induction m; intros; simpl.
    - now rewrite Natβ₁.
    - now rewrite Natβ₂, IHm.
  Defined.

  Lemma quoteLeaves : forall (t : TreeM),
    exists n, leaves (quoteTree t) = quoteNat n.
  Proof.
    intros.
    induction t ; simpl.
    rewrite ! Treeβ₁. exists 1. reflexivity.
    destruct IHt1, IHt2.
    exists (x + x0).
    rewrite ! Treeβ₂.
    simpl in *.
    rewrite H, H0, quotePlus.
    reflexivity.
  Qed.

  (* HW - hard, requires Natη *)
  (* Foleg érdekesség, my dudes *)
  Parameter (Natη : forall {A} (f : Tm Nat -> Tm A) (s : Tm A -> Tm A), (forall u, f (suc u) = s (f u)) -> forall u, f u = iteNat (f zero) s u).

  Lemma helper (t u : Tm Nat) : iteNat (suc u) suc t = suc (iteNat u suc t).
  Proof.
  Admitted.

  Goal forall (t : TreeM), leaves (quoteTree t) = leaves' (quoteTree t).
  Proof.
  Admitted.

End ExampleInds.

Module GeneralisedExampleInds.

  Parameter (Tree : Ty).
  Definition F : Ty -> Ty := fun X => ⊤ ⊎ X × X.
  Parameter (con : Tm (F Tree) -> Tm Tree).

  (* con implements leaf and node at the same time*)
  Definition leaf : Tm Tree := con (inl tt).
  Definition node (t1 t2 : Tm Tree) : Tm Tree := con (inr (t1 , t2)).

  Definition map {A B : Ty} (f : Tm A -> Tm B) (w : Tm (F A)) : Tm (F B) :=
    case w (fun _ => inl tt) (fun aa => inr (f (fst aa) , f (snd aa))).
  
  Parameter (ite : forall {A : Ty}, (Tm (F A) -> Tm A) -> Tm Tree -> Tm A).
  Parameter (Treeβ : forall {A : Ty} (c : Tm (F A) -> Tm A) (w : Tm (F Tree)), ite c (con w) = c (map (ite c) w)).

  Definition iteTree {T : Ty} (l : Tm T) (n : Tm T -> Tm T -> Tm T) (t : Tm Tree) : Tm T :=
    ite (fun x => case x (fun _ => l) (fun p => n (fst p) (snd p))) t.

  Lemma Treeβ₁ : forall {T} {l : Tm T} {n}, iteTree l n leaf = l.
  Proof.
    intros.
    cbv.
    rewrite Treeβ.
    cbv.
    rewrite ! Sumβ₁.
    reflexivity.
  Qed.

  Lemma Treeβ₂ : forall {T} {l : Tm T} {n u v}, iteTree l n (node u v) = n (iteTree l n u) (iteTree l n v).
  Proof.
    intros.
    cbv.
    rewrite Treeβ.
    cbv.
    rewrite ! Sumβ₂.
    rewrite ! Prodβ₁.
    rewrite ! Prodβ₂.
    reflexivity.
  Qed.

  (* If we hide the generalization... *)
  Opaque iteTree leaf node.

  (* ...then everything from the last module should work without changes. *)
  Parameter (Nat     : Ty).
  Parameter (zero    : Tm Nat).
  Parameter (suc     : Tm Nat -> Tm Nat).
  Parameter (iteNat  : forall {N}, Tm N -> (Tm N -> Tm N) -> Tm Nat -> Tm N).
  Parameter (Natβ₁   : forall {N} {z : Tm N} {s},   iteNat z s zero = z).
  Parameter (Natβ₂   : forall {N} {z : Tm N} {s u}, iteNat z s (suc u) = s (iteNat z s u)).

  Definition plus (a b : Tm Nat) : Tm Nat := iteNat b suc a.
  Arguments plus _ _ / : assert.

  Definition one   : Tm Nat := suc zero.
  Definition two   : Tm Nat := suc one.
  Definition three : Tm Nat := suc two.
  Definition four  : Tm Nat := suc three.
  Definition seven : Tm Nat := suc (suc (suc four)).

  Definition leaves : Tm Tree -> Tm Nat := iteTree one plus.
  Arguments leaves _ / : assert.

  Goal leaves (node (node leaf leaf) (node leaf leaf)) = four.
  Proof.
    cbv. rewrite ! Treeβ₂, ! Treeβ₁.
    repeat rewrite ! Natβ₂, ! Natβ₁.
    reflexivity.
  Qed.

  (* And so on... *)

End GeneralisedExampleInds.

Module Ind.

  (* strictly positive types *)
  Inductive SPos : (Ty -> Ty) -> Type :=
    | idP    : SPos (fun X => X)
    | constP : forall (A : Ty), SPos (fun _ => A)
    | ProdP  : forall {F G}, SPos F -> SPos G -> SPos (fun X => F X × G X)
    | SumP   : forall {F G}, SPos F -> SPos G -> SPos (fun X => F X ⊎ G X)
    | ArrP   : forall {F} (A : Ty), SPos F -> SPos (fun X => A ⇒ F X)
  .

  (* Coq also only allows strictly positive inductive types *)
  Fail Inductive X :=
    | C : (X -> X) -> X.

  Fixpoint map {F : Ty -> Ty} {A B : Ty} (FP : SPos F) (f : Tm A -> Tm B) : Tm (F A) -> Tm (F B) :=
    match FP in SPos F return Tm (F A) -> Tm (F B) with
    | idP         => f
    | constP A    => id
    | ProdP FP GP => fun t => (map FP f (fst t), map GP f (snd t))
    | SumP  FP GP => fun t => case t (fun u => inl (map FP f u)) (fun v => inr (map GP f v))
    | ArrP   A FP => fun t => lam (fun x => map FP f (t ⋅ x))
    end.

  (* F (F (F (...))) — least fixpoint *)
  (* F (fix F) = fix F *)
  Parameter Ind    : forall {F : Ty -> Ty}, SPos F -> Ty.
  Parameter con    : forall {F : Ty -> Ty} (FP : SPos F), Tm (F (Ind FP)) -> Tm (Ind FP).
  Parameter iteInd : forall {F : Ty -> Ty} (FP : SPos F) {C : Ty}, (Tm (F C) -> Tm C) -> Tm (Ind FP) -> Tm C.
  Parameter Indβ   : forall {F : Ty -> Ty} (FP : SPos F) {C : Ty} (f : Tm (F C) -> Tm C) (w : Tm (F (Ind FP))),
    iteInd FP f (con FP w) = f (map FP (iteInd FP f) w).
    (*          |--------|             |-----------|    *)
    (*         Tm (Ind FP)          Tm (Ind FP) -> Tm C *)
    (*                         |-------------------|    *)
    (*                      Tm (F (Ind FP)) -> Tm (F C) *)
  Parameter Indη   : forall {F : Ty -> Ty} (FP : SPos F) {C : Ty} (f : Tm (F C) -> Tm C) (z : Tm (Ind FP) -> Tm C),
    (forall (w : Tm (F (Ind FP))), z (con FP w) = f (map FP z w)) -> z = iteInd FP f.




  (* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
  (* ZH-RA KÉSZÜLÉS INNEN *)
  (* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)

  (* Natural numbers: *)
  Definition FNat : Ty -> Ty := fun X => ⊤ ⊎ X. (* ⊤ ⊎ (⊤ ⊎ (⊤ ⊎ ...)) *)
  Lemma NatP : SPos FNat.
  Proof.
    unfold FNat.
    apply SumP. apply constP. apply idP.
  Defined.
  Definition Nat : Ty := Ind NatP.

  Definition zero : Tm Nat := con NatP (inl tt).
  Definition suc (n : Tm Nat) : Tm Nat := con NatP (inr n).
  (* suc (suc zero) = con NatP (inr (con NatP (inr (con NatP (inl tt))))) *)

  Definition iteNat {C : Ty} (z : Tm C) (s : Tm C -> Tm C) (n : Tm Nat) : Tm C := iteInd NatP (fun x => case x (fun _ => z) (fun y => s y)) n.

  Lemma Natβ₁ : forall {C : Ty} {z : Tm C} {s : Tm C -> Tm C}, iteNat z s zero = z.
  Proof.
    intros.
    cbv. rewrite Indβ.
    cbv. rewrite ! Sumβ₁.
    reflexivity.
  Qed.

  Lemma Natβ₂ : forall {C : Ty} {z : Tm C} {s : Tm C -> Tm C} {n : Tm Nat}, iteNat z s (suc n) = s (iteNat z s n).
  Proof.
    intros.
    cbv. rewrite Indβ.
    cbv. rewrite ! Sumβ₂.
    reflexivity.
  Qed.

  (* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)  
  (* ZH-RA KÉSZÜLÉS IDÁIG *)
  (* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)




  (* Opaque Nat zero suc iteNat. *)

  (* Everything that we have done with explicit Nat can be reproduced: *)
  Definition plus (a b : Tm Nat) : Tm Nat := iteNat b suc a.

  Goal plus (suc zero) (suc zero) = suc (suc zero).
  Proof.
    cbv -[zero suc iteNat].
    now rewrite Natβ₂, Natβ₁.
  Qed.

  (* optional exercises: prove η for Nat (from the η for general ind types above), show that plus is assoc, idl, idr, and so on. *)

  (* binary trees: *)
  Definition BinTreeF : Ty -> Ty := fun X => ⊤ ⊎ (X × X).
  Lemma BinTreeP : SPos BinTreeF.
  Proof.
    cbv.
    apply SumP. apply constP.
    apply ProdP ; apply idP.
  Defined.
  Definition BinTree := Ind BinTreeP.

  Definition leaf : Tm BinTree := con BinTreeP (inl tt).
  Definition node (l r : Tm BinTree) : Tm BinTree := con BinTreeP (inr (l, r)).

  Definition iteTree {T : Ty} (l : Tm T) (n : Tm T -> Tm T -> Tm T) (t : Tm BinTree) : Tm T. Admitted.

  Lemma Treeβ₁ {T} {l : Tm T} {n : Tm T -> Tm T -> Tm T} : iteTree l n leaf = l.
  Proof.
  Admitted.

  Lemma Treeβ₂ {T} {l : Tm T} {n : Tm T -> Tm T -> Tm T} {t u : Tm BinTree} : iteTree l n (node t u) = n (iteTree l n t) (iteTree l n u).
  Proof.
  Admitted.

  (* lists: *)
  (*
     data List a = Nil | Cons a (List a)
   *)
  Definition ListF (A : Ty) : Ty -> Ty := fun X => ⊤ ⊎ (A × X).
  Lemma ListP (A : Ty) : SPos (ListF A).
  Proof.
  Admitted.
  Definition List (A : Ty) := Ind (ListP A).

  (* HF: constructors: nil, cons *)
  (* (iterator same as foldr in Haskell) *)

  (* binary trees with nat at leaves: *)
  Definition BinTreeNatF : Ty -> Ty := fun X => Nat ⊎ (X × X).
  Lemma BinTreeNatP : SPos BinTreeNatF.
  Proof.
  Admitted.
  Definition BinTreeNat := Ind BinTreeNatP.

  (* HW: constructors and iterator *)

  Definition BinTree2F : Ty -> Ty. Admitted.
  Lemma BinTree2P : SPos BinTree2F.
  Proof.
  Admitted.
  Definition BinTree2 := Ind BinTree2P.

  (* 3-branching trees: *)
  Definition ThreeTreeF : Ty -> Ty := fun X => ⊤ ⊎ (X × X × X).
  Lemma ThreeTreeP : SPos ThreeTreeF.
  Proof.
    unfold ThreeTreeF.
    apply SumP.
    apply constP.
    apply ProdP.
    apply idP.
    apply ProdP.
    apply idP.
    apply idP.
  Defined.
  Definition ThreeTree := Ind ThreeTreeP.

  (* infinitely branching trees: *)
  Definition InfTreeF : Ty -> Ty := fun X => ⊤ ⊎ (Nat ⇒ X).
  Lemma InfTreeP : SPos InfTreeF.
  Proof.
    unfold InfTreeF.
    apply SumP.
    apply constP.
    apply ArrP.
    apply idP.
  Defined.
  Definition InfTree := Ind InfTreeP.

  Definition BoolF : Ty -> Ty := fun X => ⊤ ⊎ ⊤.
  Lemma BoolP : SPos BoolF.
  Proof.
    unfold BoolF.
    apply SumP.
    apply constP.
    apply constP.
  Defined.
  Definition Bool : Ty := Ind BoolP.
  (* do the rest *)

End Ind.

