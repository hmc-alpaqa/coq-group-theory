From Group Require Export group_theory.


Section test_proof.


(* Proof using the is_abelian notation. *)
Lemma boolean_implies_abelian : (forall x : group_theory.G, x <*> x = e) -> (is_abelian group_theory.G).
Proof.
  intros.

  (* sub-environment for showing commutativity *)
  assert (forall (a b : group_theory.G), a <*> b = b <*> a).
  intros.
  
    assert ( (a <*> b) <*> (a <*> b) = e).
    apply H.
    assert ( a <*> b = a <*> b ).
    reflexivity.
    rewrite <- (mult_e a) in H1 at 2.
    rewrite <- H0 in H1.
    repeat rewrite mult_assoc in H1.

    assert (a <*> a = e).
    apply H.
    assert (b <*> b = e).
    apply H.
    
    rewrite H2 in H1.
    rewrite <- mult_assoc in H1.
    rewrite H3 in H1.
    rewrite e_mult in H1.
    rewrite mult_e in H1.
  
  exact H1.  
  (* Exit that sub-environment. *)

  unfold is_abelian.
  exact H0.
 Qed.

(* Proof without is_abelian notation *)
Theorem t1 (G : group_theory.Group) (H: forall (x : group_theory.G), x <*> x = e) : (forall (a b : group_theory.G), a <*> b = b <*> a).
Proof.
  intros.
  (* assert ( a <*> b : A group_theory.G) *)
  assert ( (a <*> b) <*> (a <*> b) = e).
  apply H.

  assert ( (a <*> b) = (a <*> b) ).
  reflexivity.
  rewrite <- (mult_e a) in H1 at 2.
  rewrite <- H0 in H1.
  repeat rewrite mult_assoc in H1.
  
  assert ( (a <*> a) = e ).
  apply H.
  assert ( (b <*> b) = e ).
  apply H.

  rewrite H2 in H1.
  rewrite <- mult_assoc in H1.
  rewrite H3 in H1.
  rewrite (e_mult b) in H1.
  rewrite mult_e in H1.
  exact H1.
Qed.

(* Proof using our custom tactics *)
Theorem t2 : (forall (x : group_theory.G), x <*> x = e) -> (forall (a b : group_theory.G), a <*> b = b<*>a). 
Proof.
intros .
assert_and_simpl (a<*>b) (a<*>e<*>b).
user_assert_equal (a<*>e<*>b) (a<*>((a<*>b)<*>(a<*>b))<*>b ).
now rewrite <- (H (a<*>b)).
assert_and_simpl (a <*> (a <*> b <*> (a <*> b)) <*> b) (a<*>a<*>(b<*>a)<*>(b<*>b)).
user_assert_equal (a<*>a<*>(b<*>a)<*>(b<*>b)) (e<*>(b<*>a)<*>(b<*>b)).
now rewrite (H a).
user_assert_equal  (e<*>(b<*>a)<*>(b<*>b)) (e<*>(b<*>a)<*>e).
now rewrite (H b).
group.
Qed.

End test_proof.

  