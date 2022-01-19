Section LP1.
Variables P Q R S T : Prop.
(* 1 *)
Lemma weak_peirce : ((((P -> Q) -> P) -> P) -> Q) -> Q.
Proof.
intro.
apply H.
intros.
apply H0.
intro.
apply H.
intro.
assumption.
Qed.
(* 2 *)
Lemma then_bsc : (P -> Q) -> (Q -> R) -> P -> R.
Proof.
intros.
apply H0.
apply H.
assumption.
Qed.
(* 3 *)
Lemma contraposition : ((P -> Q) -> (~Q -> ~P)).
Proof.
intro.
intro.
intro.
apply H0.
apply H.
assumption.
Qed.
(* 4 *)
Lemma contraposition' : (~P -> ~Q) <-> (~~Q -> ~~P).
Proof.
split.
intros.
intro.
apply H0.
apply H.
assumption.
intro.
intro.
intro.
apply H.
intro.
apply H2.
exact H1.
intro.
apply H0.
assumption.
Qed.
(* 5 *)
Lemma impl_cmpl : (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
split.
intro.
apply H0.
apply H.
assumption.
intro.
apply H.
apply H0.
assumption.
Qed.
(* 6 *)
Lemma then_ext : (P -> Q) -> (P -> R) -> (Q -> R -> S) -> P -> S.
Proof.
intros.
apply H1.
apply H.
assumption.
apply H0.
assumption.
Qed.
End LP1.
Section LP2.
Variables P Q R S T : Prop.
(* 7 *)
Lemma and_assoc : P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
intro.
split.
split.
destruct H.
assumption.
destruct H as [H1 H2].
destruct H2 as [H2 H3].
assumption.
destruct H.
destruct H0.
assumption.
Qed.
(* 8 *)
Lemma and_imp_dist : (P -> Q) /\ (R -> S) -> P /\ R -> Q /\ S.
Proof.
intro.
split.
destruct H.
destruct H0.
apply H.
assumption.
destruct H.
destruct H0.
apply H1.
assumption.
Qed.
(* 9 *)
Lemma or_and_not : (P \/ Q) /\ ~P -> Q.
Proof.
intro.
destruct H.
destruct H as [H1 | H2].
elim H0.
apply H1.
assumption.
Qed.
(* 10 - Resolver usando Contradicction *)
Lemma not_contrad : ~(P /\ ~P).
Proof.
unfold not.
intros.
destruct H.
apply H0.
contradiction.
Qed.
(* 11 *)
Lemma De_morgan_1 : ~(P \/ Q) -> ~P /\ ~Q.
Proof.
unfold not.
split.
intros.
apply H.
left.
assumption.
intro.
apply H.
right.
assumption.
Qed.
(* 12 *)
Lemma De_morgan_2 : ~P /\ ~Q -> ~(P \/ Q).
Proof.
unfold not.
intros.
destruct H.
destruct H0.
apply H.
assumption.
apply H1.
assumption.
Qed.
(* 13 *)
Lemma De_morgan_3 : ~P \/ ~Q -> ~(P /\ Q).
Proof.
unfold not.
intros.
destruct H.
destruct H0.
apply H.
assumption.
destruct H0.
apply H.
assumption.
Qed.
(* 14 *)
Lemma b_mix : P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
split.
intro.
destruct H.
split.
left.
assumption.
left.
assumption.
split.
destruct H.
right.
assumption.
destruct H.
right.
assumption.
intro.
destruct H.
destruct H.
destruct H0.
left.
assumption.
left.
assumption.
destruct H0.
left.
assumption.
right.
split.
assumption.
assumption.
Qed.
End LP2.
(* 15 *)
Section S0.
Variables P Q : Prop.
Hypothesis H0 : P -> Q.
Hypothesis H1 : ~P -> Q.
Lemma weak_exm : ~~Q.
Proof.
intro.
apply H.
apply H1.
intro.
apply H.
apply H0.
assumption.
Qed.
End S0.
(* 16 *)
Section S1.
Variables P Q R S : Prop.
Hypothesis H : Q -> P.
Hypothesis H0 : P <-> (R /\ S).
Hypothesis H1 : ~S.
Lemma aprobar_logica : ~Q.
Proof.
intro.
apply H1.
destruct H0.
destruct H3.
apply H.
assumption.
assumption.
Qed.
End S1.
