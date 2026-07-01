(* polynomial and pos/neg type operators *)

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

Definition Bool    := ⊤ ⊎ ⊤.
Definition true    :  Tm Bool := inl tt.
Definition false   :  Tm Bool := inr tt.
Definition ite {A  :  Ty} (t : Tm Bool) (u : Tm A) (v : Tm A) : Tm A :=
  case t (fun _ => u) (fun _ => v).
Proposition Boolβ₁ :  forall {A} {u v : Tm A}, ite true u v = u.
Proof.
  intros. unfold ite. unfold true. rewrite Sumβ₁. reflexivity.
Qed.
Proposition Boolβ₂ :  forall {A} {u v : Tm A}, ite false u v = v.
Proof.
  intros. cbv. rewrite Sumβ₂. reflexivity.
Qed.

Module Poly.

  Inductive Poly : (Ty -> Ty) -> Type :=
    | idPoly    : Poly (fun X => X)
    | ProdPoly  : forall {F G}, Poly F -> Poly G -> Poly (fun X => F X × G X)
    | UnitPoly  : Poly (fun X => ⊤)
    | SumPoly   : forall {F G}, Poly F -> Poly G -> Poly (fun X => F X ⊎ G X)
    | EmptyPoly : Poly (fun X => ⊥)
  .

  Fixpoint map {F : Ty -> Ty} {A B : Ty} (Fpoly : Poly F) (f : Tm A -> Tm B) :
    Tm (F A) -> Tm (F B) :=
    match Fpoly in Poly F return Tm (F A) -> Tm (F B) with
    | idPoly                        => f
    | ProdPoly FPoly GPoly => fun t => (map FPoly f (fst t), map GPoly f (snd t))
    | UnitPoly                     => fun t => tt
    | SumPoly  FPoly GPoly => fun t => case t (fun u => inl (map FPoly f u)) (fun v => inr (map GPoly f v))
    | EmptyPoly                  => exfalso
    end.

  Definition map' {F : Ty -> Ty} {A B : Ty} (Fpoly : Poly F) (f : Tm A -> Tm B)
    : Tm (F A) -> Tm (F B).
  Proof.
    induction Fpoly.
    - exact f.
    - intro w. apply pair.
      + exact (IHFpoly1 (fst w)).
      + exact (IHFpoly2 (snd w)).
    - intro. exact tt.
    - intro w. apply (case w).
      + intro u. exact (inl (IHFpoly1 u)).
      + intro v. exact (inr (IHFpoly2 v)).
    - exact exfalso.
  Defined.
  Print map'.

  Definition neg (b : Tm Bool) : Tm Bool := ite b false true.
  Arguments neg _ /.

  Lemma poly4Tuple : Poly (fun X => X × X × X × X).  (* X × (X × (X × X)) *)
  Proof.
    apply ProdPoly.
    apply idPoly.
    apply ProdPoly.
    apply idPoly.
    apply ProdPoly.
    apply idPoly.
    apply idPoly.
    
    Restart.
    
    apply ProdPoly, ProdPoly, ProdPoly ; apply idPoly.

(*  !!!TILOS!!!
    Restart.
    repeat constructor.
    !!!TILOS!!!
*)
  Defined.

  Goal map poly4Tuple neg (true, (false, (true, false))) =
  (false, (true, (false, true))).
  Proof.
    simpl.
    rewrite ! Prodβ₂.
    rewrite ! Prodβ₁.
    rewrite ! Boolβ₁.
    rewrite ! Boolβ₂.
    reflexivity.
  Qed.

  (* 0 + 1x + x^2 *)
  Goal Poly (fun X => ⊥ ⊎ (⊤ × X) ⊎ X × X).  (* ⊥ ⊎ ((⊤ × X) ⊎ (X × X)) *)
  Proof.
    apply SumPoly.
    apply EmptyPoly.
    apply SumPoly.
    apply ProdPoly.
    apply UnitPoly.
    apply idPoly.
    apply ProdPoly.
    apply idPoly.
    apply idPoly.
  Qed.

  Lemma BoolPoly : Poly (fun X => Bool).
  Proof.
    apply SumPoly.
    apply UnitPoly.
    apply UnitPoly.
  Defined.

  Definition F : Ty -> Ty := fun X => ⊤ ⊎ Bool × X.
  Lemma Fpoly : Poly F.
  Proof.
    unfold F.
(*  cbv. *)
    apply SumPoly.
    apply UnitPoly.
    apply ProdPoly.
    apply SumPoly.
    apply UnitPoly.
    apply UnitPoly.
    apply idPoly.
  Defined.

  Goal forall {A B : Ty} {f : Tm A -> Tm B} {t : Tm A},
    map Fpoly f (inr (true , t)) = inr (true , f t).
  Proof.
    intros.
    simpl.
    rewrite ! Sumβ₂.
    rewrite ! Prodβ₁.
    rewrite ! Prodβ₂.
    unfold true.
    rewrite ! Sumβ₁.
    reflexivity.
    (* solve Fpoly first *)
  Qed.

  Goal forall {F : Ty -> Ty} {FPoly : Poly F} {A : Ty} {u : Tm (F A)},
    map FPoly (fun x => x) u = u.
  Proof.
    intros.
    induction FPoly ; simpl.
    * reflexivity.
    * rewrite IHFPoly1. rewrite IHFPoly2. rewrite Prodη. reflexivity.
    * rewrite Unitη. reflexivity.
    * rewrite (Sumη (fun x => x) u) at 2. f_equal. extensionality x. now rewrite IHFPoly1. admit.
    * now rewrite (Emptyη (fun x => x) u ) at 2.
  Admitted.

  Goal forall {F : Ty -> Ty} {FPoly : Poly F} {A B C : Ty} {g : Tm A -> Tm B} {f : Tm B -> Tm C} {w : Tm (F A)},
    map FPoly (fun x => f (g x)) w = map FPoly f (map FPoly g w).
  Proof.
    intros.
  Admitted.

End Poly.

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

  Goal Pos (fun X => X ⇒ Bool ⇒ Bool) + Neg (fun X => X ⇒ Bool ⇒ Bool).
  Proof.
    right.
    apply ArrNeg.
    apply idPos.
    apply constNeg.

(*
    !!!TILOS!!!
    Restart.

    right. repeat constructor.

    Restart.

    solve [repeat constructor].

    !!!TILOS!!!
*)
  Qed.

  Goal Pos (fun X => (X ⇒ Bool) ⇒ X) + Neg (fun X => (X ⇒ Bool) ⇒ X).
  Proof.
  Admitted.

  Goal Pos (fun X => ((X ⇒ Bool) ⇒ Bool) ⇒ Bool) + Neg (fun X => ((X ⇒ Bool) ⇒ Bool) ⇒ Bool).
  Proof.
  Admitted.

  Goal Pos (fun X => (Bool ⇒ Bool) ⇒ X ⊎ X) + Neg (fun X => (Bool ⇒ Bool) ⇒ X ⊎ X).
  Proof.
  Admitted.

  Goal Pos (fun X => (X × (X ⊎ ⊤)) ⇒ Bool) + Neg (fun X => (X × (X ⊎ ⊤)) ⇒ Bool).
  Proof.
  Admitted.

  Goal Pos (fun X => (Bool ⇒ Bool) ⇒ ⊤) + Neg (fun X => (Bool ⇒ Bool) ⇒ ⊤).
  Proof.
    left. apply constPos.
    Restart.
    right. apply constNeg.
  Qed.

  Definition Thing (X : Ty) : Ty := ⊤ ⇒ X.

  Lemma PosThing : Pos Thing.
  Proof.
    unfold Thing.
    apply ArrPos.
    apply constNeg.
    apply idPos.
  Defined.

  Definition neg (b : Tm Bool) : Tm Bool := ite b false true.

  Goal mapP PosThing neg (λ x, true) = λ x, false.
  Proof.
    simpl.
    f_equal.
    extensionality x.
    rewrite arrβ.
    unfold neg.
    rewrite Boolβ₁.
    reflexivity.
  Qed.

  Definition Thing2 (X : Ty) : Ty := X ⇒ Bool.

  Lemma NegThing2 : Neg Thing2.
  Proof.
    repeat constructor.
  Defined.

  Goal mapN NegThing2 neg (λ x, x) = λ x, neg x.
  Proof.
    simpl.
    f_equal.
    extensionality x.
    now rewrite arrβ.
  Qed.

  Goal forall F (PosF : Pos F) A (u : Tm (F A)), mapP PosF (fun x => x) u = u.
  Proof.
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

Module PosNegClass.

  Class Pos (F : Ty -> Ty) : Type := {
    mapP : forall {A B}, (Tm A -> Tm B) -> Tm (F A) -> Tm (F B)
  }.

  Class Neg (F : Ty -> Ty) : Type := {
    mapN : forall {A B}, (Tm A -> Tm B) -> Tm (F B) -> Tm (F A)
  }.

  Instance idPos : Pos (fun X => X) := {|
    mapP _ _ f := f
  |}.

  Instance constPos C : Pos (fun _ => C) := {|
    mapP _ _ _ (c : Tm C) := c
  |}.

  Instance constNeg C : Neg (fun _ => C) := {|
    mapN _ _ _ (c : Tm C) := c
  |}.

  Instance SumPos F G `{PosF : Pos F} `{PosG : Pos G} : Pos (fun X => F X ⊎ G X) := {|
   mapP _ _ f w := case w (fun u => inl (mapP f u)) (fun v => inr (mapP f v))
  |}.

  Instance SumNeg F G `{NegF : Neg F} `{NegG : Neg G} : Neg (fun X => F X ⊎ G X) := {|
   mapN _ _ f w := case w (fun u => inl (mapN f u)) (fun v => inr (mapN f v))
  |}.

  Instance ProdPos F G `{PosF : Pos F} `{PosG : Pos G} : Pos (fun X => F X × G X) := {|
    mapP _ _ f w := mapP f (fst w), mapP f (snd w)
  |}.

  Instance ProdNeg F G `{NegF : Neg F} `{NegG : Neg G} : Neg (fun X => F X × G X) := {|
    mapN _ _ f w := mapN f (fst w), mapN f (snd w)
  |}.

  Instance ArrPos F G `{NegF : Neg F} `{PosG : Pos G} : Pos (fun X => F X ⇒ G X) := {|
    mapP _ _ f g := lam (fun x => mapP f (g ⋅ (mapN f x)))
  |}.

  Instance ArrNeg F G `{PosF : Pos F} `{NegG : Neg G} : Neg (fun X => F X ⇒ G X) := {|
    mapN _ _ f g := lam (fun x => mapN f (g ⋅ (mapP f x)))
  |}.

  Goal Pos (fun X => (X × (X ⊎ ⊤)) ⇒ Bool) + Neg (fun X => (X × (X ⊎ ⊤)) ⇒ Bool).
  Proof.
  Admitted.

  Definition Thing (X : Ty) : Ty := ⊤ ⇒ X.

  Lemma PosThing : Pos Thing.
  Proof.
  Admitted.

  Definition neg (b : Tm Bool) : Tm Bool := ite b false true.

  Goal mapP (Pos := PosThing) neg (λ x, true) = λ x, false.
  Proof.
  Admitted.

End PosNegClass.

Module Tree.

  (* remember natural numbers *)
  Parameter (Nat     : Ty).
  Parameter (zero    : Tm Nat).
  Parameter (suc     : Tm Nat -> Tm Nat).
  Parameter (iteNat  : forall {N}, Tm N -> (Tm N -> Tm N) -> Tm Nat -> Tm N).
  Parameter (Natβ₁   : forall {N} {z : Tm N} {s},   iteNat z s zero = z).
  Parameter (Natβ₂   : forall {N} {z : Tm N} {s u}, iteNat z s (suc u) = s (iteNat z s u)).

  Definition plus : Tm Nat -> Tm Nat -> Tm Nat :=
    fun a b => iteNat b suc a.
  Arguments plus _ _ /.

  Definition one   : Tm Nat := suc zero.
  Definition two   : Tm Nat := suc one.
  Definition three : Tm Nat := suc two.
  Definition four  : Tm Nat := suc three.
  Definition seven : Tm Nat := suc (suc (suc four)).

  Goal plus (suc zero) (suc (suc zero)) = suc (suc (suc zero)).
  Proof.
    simpl. now rewrite Natβ₂, Natβ₁.
  Qed.

  (* we extend the language with binary trees *)
  Parameter (Tree    : Ty).
  Parameter (leaf    : Tm Tree).
  Parameter (node    : Tm Tree -> Tm Tree -> Tm Tree).
  Parameter (iteTree : forall {T}, Tm T -> (Tm T -> Tm T -> Tm T) -> Tm Tree -> Tm T).
  Parameter (Treeβ₁  : forall {T} {l : Tm T} {n}, iteTree l n leaf = l).
  Parameter (Treeβ₂  : forall {T} {l : Tm T} {n u v},
    iteTree l n (node u v) = n (iteTree l n u) (iteTree l n v)).

  Definition leaves : Tm (Tree ⇒ Nat) := lam (iteTree one plus).
  Arguments leaves /.

  Goal leaves ⋅ (node (node leaf leaf) (node leaf leaf)) = four.
  Proof.
  Admitted.

  Definition leaves' : Tm (Tree ⇒ Nat) :=
    lam (fun t => suc (iteTree zero (fun t1 t2 => suc (plus t1 t2)) t)).
  Arguments leaves' /.

  Goal leaves' ⋅ (node (node leaf leaf) (node leaf leaf)) = four.
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
  Admitted.

  Lemma quoteLeaves : forall (t : TreeM),
    exists n, leaves ⋅ quoteTree t = quoteNat n.
  Proof.
  Admitted.

  Goal forall (t : TreeM), leaves ⋅ quoteTree t = leaves' ⋅ quoteTree t.
  Proof.
    (* HW - hard *)
  Admitted.

End Tree.
