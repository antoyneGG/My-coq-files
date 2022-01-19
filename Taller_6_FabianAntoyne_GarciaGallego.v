Section LPPO_1.
Variable D: Set.
Variable c d e :D.
Variable P Q T: D-> Prop.
(*1*)
Theorem pred_008 : ~(forall x, P x) -> ~ forall x, P x /\ Q x.
Proof.
intros.
intro.
apply H.
intro.
destruct H.
intro x0.
apply H0.
Qed.
(*2*)
Theorem pred_013 : (exists x, P x \/ Q x) -> (forall x, ~Q x) -> exists x, P x.
Proof.
intro.
destruct H.
exists x.
destruct H.
assumption.
apply H0 in H.
contradiction.
Qed.
(*3*)
Theorem pred_025 : ~(forall x, P x /\ Q x) /\ (forall x, P x) -> ~forall x, Q x.
Proof.
intros.
intro.
destruct H.
apply H.
intro.
split.
apply H1.
apply H0.
Qed.
(*4*)
Theorem pred_035 : (forall y, Q y -> ~exists x, P x) /\ (forall x, P x) -> forall y, ~Q y.
Proof.
intro.
destruct H.
intros.
intro.
apply H in H1.
apply H1.
exists y.
apply H0.
Qed.
(*5*)
Theorem pred_067 : (forall x, ~P x) -> ~exists x, P x.
Proof.
intros.
intro.
destruct H0.
apply H in H0.
assumption.
Qed.
End LPPO_1.
Section LPPO_2.
Variable A : Set.
Variables (P Q : A -> Prop)
(R : A -> A -> Prop).
(*6*)
Lemma forall_imp_dist : (forall x:A, P x -> Q x) ->
(forall x:A, P x) ->
forall x: A, Q x.
Proof.
intros.
apply H.
apply H0.
Qed.
(*7*)
Lemma forall_perm : (forall x y:A, R x y) -> forall y x, R x y.
Proof.
intros.
apply H.
Qed.
(*8*)
Lemma forall_delta : (forall x y:A, R x y) -> forall x, R x x.
Proof.
intros.
apply H.
Qed.
(*9*)
Lemma exists_or_dist : (exists x: A, P x \/ Q x) <->
(exists x, P x) \/ (exists x , Q x).
Proof.
split.
intros.
destruct H.
destruct H.
left.
exists x.
assumption.
right.
exists x.
assumption.
intros.
destruct H.
destruct H.
exists x.
left.
assumption.
destruct H.
exists x.
right.
assumption.
Qed.
(*10*)
Lemma exists_imp_dist : (exists x: A, P x -> Q x) ->
(forall x:A, P x) ->
exists x:A, Q x.
Proof.
intros.
destruct H.
exists x.
apply H.
apply H0.
Qed.
(*11*)
Lemma not_empty_forall_exists : forall a:A,
(forall x:A, P x) ->
exists x:A, P x.
Proof.
intros.
exists a.
apply H.
Qed.
(*12*)
Lemma not_ex_forall_not : ~(exists x:A, P x) <-> forall x:A, ~P x.
Proof.
split.
intros.
intro.
apply H.
exists x.
assumption.
intros.
intro.
destruct H0.
apply H in H0.
assumption.
Qed.
End LPPO_2.
