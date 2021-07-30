
Require Setoid.

Record Group : Type := 
{
  (* coercion allows for the common mathematical abuse of notation 'let x be in the group G.'*)
  A :> Set;

  mult : A -> A -> A ;
  inv : A -> A ;
  e : A ; 

  mult_assoc : forall a b c, mult a (mult b c) = mult (mult a b) c;
  mult_e : forall a, mult a e = a;
  mult_inv : forall a, mult a (inv a) = e;
}.

(* Infer the group at hand from type of other arguments for convenience. *)
Arguments e {g}.
Arguments mult {g} _ _.
Arguments inv {g} _.
Arguments mult_assoc {g} _ _ _.
Arguments mult_inv {g} _ .
Arguments mult_e {g} _ .




(* syntactic sugar for the binary operation *)
Notation "x <*> y" := (mult x y) (at level 50, left associativity).


 
Variable (G : Group).
(* 
  The next two theorems are sometimes included as part of the group axioms,
  but are technically derivable from the axioms set above. 
*)

(*Proof that right inverse is also left inverse*)
Theorem inv_mult : forall a:G, (inv a) <*> a = e.
Proof.
  intro a.
  rewrite <- (mult_e a) at 2.
  rewrite <- (mult_inv (inv a)) at 1.
  rewrite (mult_assoc a (inv a) (inv (inv a))).
  rewrite (mult_inv a).
  rewrite mult_assoc.
  rewrite mult_e.
  rewrite mult_inv.
  reflexivity.
Qed.

(*Proof that right identity is also left identity.*)
Theorem e_mult : forall a:G, e <*> a = a.
Proof.
  intro a.
  rewrite <- (mult_inv a) at 1.
  rewrite <- mult_assoc.
  rewrite (inv_mult a).
  rewrite mult_e.
  reflexivity.
Qed.

(*Proof that (ab)^-1 = b^-1 a^-1*)
Theorem product_inv : forall (a b : G), inv( a <*> b ) = (inv b) <*> (inv a).
Proof.
  intros a b.
  rewrite <- e_mult at 1.
  rewrite <- (inv_mult b).
  rewrite <- (e_mult b) at 2.
  rewrite <- (inv_mult a).
  rewrite <- (mult_assoc (inv a) a b).
  rewrite mult_assoc.
  rewrite <- (mult_assoc ((inv b) <*> (inv a)) (a <*> b) _).
  rewrite mult_inv.
  rewrite mult_e.
  reflexivity.
Qed.

(*ab = ac -> b = c*)
Lemma left_cancellation : forall (a b c : G), a<*>b = a<*>c -> b = c.
Proof.
  intros.
  rewrite <- (e_mult b).
  rewrite <- (e_mult c).
  rewrite <- (inv_mult a).
  rewrite <- mult_assoc.
  rewrite <- mult_assoc.
  rewrite H.
  reflexivity.
Qed.

(*ab = ac <-> b = c*)
Theorem left_mult_cancel : forall (a b c : G), a<*>b = a<*>c <-> b = c.
Proof.
  split.
  generalize a b c.
  exact left_cancellation.
  intro H.
  rewrite H.
  reflexivity.
Qed.

(*ba = ca <-> b = c*)
Theorem right_mult_cancel : forall (a b c : G), b<*>a = c<*>a <-> b = c.
Proof.
  split.
  intros.
  rewrite <- (mult_e b).
  rewrite <- (mult_e c).
  rewrite <- (mult_inv a).
  repeat rewrite mult_assoc.
  rewrite H.
  reflexivity.
  intros.
  rewrite H.
  reflexivity.
Qed.

Theorem left_e_unique : (forall i : G, (forall a:G, i<*>a = a) -> i=e).
Proof. 
  intros.
  rewrite <- (right_mult_cancel e).
  rewrite (e_mult).
  rewrite (H e).
  easy.
Qed.

Theorem left_inv_unique : (forall (a b : G), b<*>a = e -> b=inv a).
Proof.
  intros.
  rewrite <- (right_mult_cancel a).
  rewrite H.
  now rewrite inv_mult.
Qed.

Theorem double_inv : (forall a : G, inv (inv a ) = a).
Proof.
intros.
rewrite <- (right_mult_cancel (inv a)).
rewrite mult_inv.
now rewrite inv_mult.
Qed.




(* Definition of abelian group. *)
Definition is_abelian (G : Group) : Prop := (forall (a b : G), a <*> b = b <*> a).

Ltac group := 
                   now repeat rewrite mult_assoc
                 + now repeat rewrite <- mult_assoc
                 + now rewrite mult_e  
                 + now rewrite e_mult
                 + now repeat (rewrite mult_e ; rewrite e_mult)
                 + now rewrite <- mult_e 
                 + now rewrite <- e_mult 
                 + now rewrite mult_inv
                 + now rewrite inv_mult
                 + now rewrite mult_inv.


Ltac user_assert_equal t t' := replace t with t' ;  swap 1 2 .

Ltac assert_and_simpl t t' := user_assert_equal t t' ; try group. 


Ltac apply_result result_name :=   rewrite <- result_name ||  rewrite result_name; try easy.




(* Proof using our custom tactics *)
Theorem t2 : (forall (x : group_theory.G), x <*> x = e) -> (forall (a b : group_theory.G), a <*> b = b<*>a). 
Proof.
intros .
assert_and_simpl (a<*>b) (a<*>e<*>b).
user_assert_equal (a<*>e<*>b) (a<*>((a<*>b)<*>(a<*>b))<*>b ).
apply_result (H (a<*>b)).
assert_and_simpl (a <*> (a <*> b <*> (a <*> b)) <*> b) (a<*>a<*>(b<*>a)<*>(b<*>b)).
user_assert_equal (a<*>a<*>(b<*>a)<*>(b<*>b)) (e<*>(b<*>a)<*>(b<*>b)).
apply_result (H a).
user_assert_equal  (e<*>(b<*>a)<*>(b<*>b)) (e<*>(b<*>a)<*>e).
apply_result (H b).
group.
Qed.







(* Hannah's proof *)
Theorem t3 : (forall (x : group_theory.G), x <*> x = e) -> (forall (a b : group_theory.G), a <*> b = b<*>a). 
Proof.
intros.
assert (forall x: group_theory.G, x = (inv x)).
intro.
apply_result (right_mult_cancel x).
rewrite H.
group.
user_assert_equal (a<*>b) (inv (a<*>b)).
apply_result (H0 (a<*>b)).
user_assert_equal (inv (a<*>b)) (inv b <*> inv a).
apply_result product_inv.
apply_result H0.
apply_result H0.
Qed.


