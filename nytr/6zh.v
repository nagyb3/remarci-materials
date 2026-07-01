(* BEGIN FIX *)
Parameter Ty : Type.
Parameter Tm : Ty -> Type.

Parameter arr        : Ty -> Ty -> Ty.
Notation "A ⇒ B"     := (arr A B) (at level 80, right associativity). (* \Rightarrow *)
Parameter app        : forall {A B : Ty}, Tm(A ⇒ B) -> Tm A -> Tm B.
Notation "x ⋅ y"     := (app x y) (at level 50, left associativity). (* \cdot *)
Parameter lam        : forall {A B : Ty}, (Tm A -> Tm B) -> Tm (A ⇒ B).
Notation "'λ' x , f" := (lam (fun x => f)) (at level 51, x name, only parsing). (* \lambda *)
Parameter arrβ       : forall {A B : Ty} (b : Tm A -> Tm B) (a : Tm A), lam b ⋅ a = b a. (* \beta *)
Parameter arrη       : forall {A B : Ty} (f : Tm (A ⇒ B)), f = lam (fun a => f ⋅ a). (* \eta *)

Parameter Bool   : Ty.
Parameter true   : Tm Bool.
Parameter false  : Tm Bool.
Parameter ite    : forall {A : Ty} (t : Tm Bool) (u v : Tm A), Tm A.
Parameter Boolβ₁ : forall {A} {u v : Tm A}, ite true u v = u.
Parameter Boolβ₂ : forall {A} {u v : Tm A}, ite false u v = v.
Parameter Boolη  : forall {A} (t : Tm Bool -> Tm A) (b : Tm Bool),
  t b = ite b (t true) (t false).

Definition and (a b : Tm Bool) : Tm Bool := ite a b false.
Arguments and _ _ / : assert.

(* TIPP:
 * Goal-ban lévő egyenlőséget `symmetry`-vel lehet megfordítani,
 * egyenlőséggel fordított írányban átírni pedig a `rewrite <-` taktikával.
 *)

Goal forall a, and a true = a.
Proof.
(* END FIX *)
  intros.
  cbv.
  symmetry.
  apply (Boolη (fun x => x) a).
(* BEGIN FIX *)
Qed.

(* TIPP:
 * Milyen jó lenne, ha ugyanaz a változó lenne mindkét ite paramétere...
 *)

Goal forall a b, and a b = and b a.
Proof.
(* END FIX *)
  intros.
  simpl.
  rewrite (Boolη (fun a => ite b a false) a).
  f_equal.
  now rewrite <- (Boolη (fun x => x) b).
  now rewrite <- (Boolη (fun x => x) b).
(* BEGIN FIX *)
Qed.
(* END FIX *)