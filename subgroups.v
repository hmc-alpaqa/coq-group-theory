From Group Require Export group_theory.


Definition char_fun (A : Set) := A -> bool.
Definition contains (A : Set) (H : char_fun A) (a : A) := H a = true.

Arguments contains {A} _ _ .

Structure subgroup (G : Group)  : Type :=
  mkSubgroup
  {
    subgroup_char_fun :> char_fun G;
    subgroup_e : contains subgroup_char_fun e;
    subgroup_mult_closed : 
      forall a b, 
        contains subgroup_char_fun a /\ contains subgroup_char_fun b ->
          contains subgroup_char_fun (a<*>b);
   subgroup_inv_closed : forall a, contains subgroup_char_fun a -> contains subgroup_char_fun (inv a);

  }.

Structure nonempty_subset (G : Group) : Type :=
  mkSubset 
  {
    subset_char_fun :> char_fun G;
    n : G;
    nonempty : contains subset_char_fun n;
  }.

Variable S : nonempty_subset group_theory.G.

Arguments subset_char_fun {G} _ _ .
Arguments n {G} _ .


Definition subgroup_crit_condition := forall (a b : group_theory.G), contains (subset_char_fun S) a /\ contains (subset_char_fun  S) b -> contains (subset_char_fun S) (a<*>inv b).


Lemma subgroup_criterion_p1 : subgroup_crit_condition -> contains (subset_char_fun S) e.
Proof. 

intros.
assert (contains (subset_char_fun S) ((n S) <*>(inv (n S)))).
apply (H (n S) (n S) ).
split.
apply (nonempty  group_theory.G S).
apply (nonempty  group_theory.G S).
rewrite <- (mult_inv (n S)).
apply H0.
Qed.





Lemma subgroup_criterion_p2 : subgroup_crit_condition ->  forall a, contains (subset_char_fun S) a -> contains (subset_char_fun S) (inv a).
Proof.
intros.
assert (contains (subset_char_fun S) e).
apply subgroup_criterion_p1.
apply H.
rewrite <- e_mult.
apply H.
easy.
Qed.



Lemma subgroup_criterion_p3 : subgroup_crit_condition ->
       forall a b, 
        contains (subset_char_fun S) a /\ contains (subset_char_fun S) b ->
          contains (subset_char_fun S) (a<*>b).
Proof. 
intros. 
assert (contains S (inv b)).
apply subgroup_criterion_p2.
trivial.
apply H0.
rewrite <- (double_inv b).
apply H.
split.
apply H0.
apply H1.
Qed.

Theorem subgroup_criterion : subgroup_crit_condition -> (subgroup group_theory.G).
Proof.
intros.
assert (contains (subset_char_fun S) e).
apply subgroup_criterion_p1.
auto.
assert (forall a b, contains (subset_char_fun S) (a<*>b)).
apply (mkSubgroup group_theory.G (subset_char_fun S) H0 subgroup_criterion_p2 subgroup_criterion_p3).
