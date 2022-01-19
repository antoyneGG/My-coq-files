Section LPPO_1.
Variable A : Set.
Variables P Q : A -> Prop.
Lemma lppo_exrc_1 :
(exists x : A, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
split.
intro.
destruct H.
destruct H.
left.
exists x.
assumption.
right.
exists x.
assumption.
intro.
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
Lemma lppo_exrc_2 : ~(exists x : A, P x) <-> forall x : A, ~P x.
Proof.
split.
intro.
intro x0.
intro.
apply H.
exists x0.
assumption.
intro.
intro.
destruct H0.
assert (H1 := H x).
apply H1.
assumption.
Qed.
End LPPO_1.

Section natProofs.
Variable a b c d: nat. (*variables de tipo nat*)

(*B) a*)
Theorem identity : forall a, a + 0 = a.
intro.
induction a0.
simpl.
reflexivity.
simpl.
rewrite IHa0.
reflexivity.
Qed.

(*B) b*)
Theorem associative : forall a b c, a + (b + c) = (a + b) + c.
intros.
induction a0.
simpl.
reflexivity.
simpl.
rewrite IHa0.
reflexivity.
Qed.

Theorem subCommutative : forall a b, S (b + a) = b + S (a).
Proof.
intros.
induction b0.
simpl.
reflexivity.
simpl.
rewrite IHb0.
reflexivity.
Qed.

(*B) c*)
Theorem commutative : forall a b, a + b = b + a.
intros.
induction a0.
simpl.
rewrite identity.
reflexivity.
simpl.
rewrite IHa0.
rewrite subCommutative.
reflexivity.
Qed.

(*B) d*)
Theorem equality: forall a b c, b = c -> b + a = c + a.
Proof.
intros.
induction a0.
rewrite identity.
rewrite -> identity.
rewrite H.
reflexivity.
rewrite commutative.
simpl.
rewrite commutative.
rewrite IHa0.
rewrite subCommutative.
reflexivity.
Qed.

(*C) a*)
Theorem multIdentity: forall a, a * 1 = a.
Proof.
intros.
induction a0.
simpl.
reflexivity.
simpl.
rewrite IHa0.
reflexivity.
Qed.

(*C) b*)
Theorem zeroProduct: forall a, a * 0 = 0.
Proof.
intros.
induction a0.
simpl.
reflexivity.
simpl.
rewrite IHa0.
reflexivity.
Qed.

Theorem auxSubCommutative: forall a b, a * b + b = b + a * b.
Proof.
intros.
induction b0.
simpl.
rewrite identity.
rewrite zeroProduct.
reflexivity.
rewrite commutative.
simpl.
reflexivity.    
Qed.

(*C) c*)
Theorem auxCommutative: forall a b, a * S b = a + a * b.
Proof.
intros.
induction a0.
simpl.
reflexivity.
simpl.
rewrite commutative.
rewrite IHa0.
rewrite commutative.
rewrite associative.
rewrite commutative.
rewrite associative.
rewrite commutative.
rewrite auxSubCommutative.
reflexivity.
Qed.

(*C) d*)
Theorem multCommutative: forall a b, a * b = b * a.
Proof.
intros.
induction b0.
simpl.
rewrite zeroProduct.
reflexivity.
simpl.
rewrite auxCommutative.
rewrite IHb0.
reflexivity.
Qed.

(*C) e*)
Theorem multDistributive: forall a b c, a * (b + c) = (a * b) + (a * c).
Proof.
intros.
induction a0.
simpl.
reflexivity.
simpl.
rewrite IHa0.
rewrite associative.
rewrite commutative.
assert (H: b0 + c0 = c0 + b0).
rewrite commutative.
reflexivity.
rewrite H.
rewrite commutative.
assert (H1: c0 + b0 + a0 * b0 = c0 + (b0 + a0 * b0)).
rewrite associative.
reflexivity.
assert (H2: c0 + (b0 + a0 * b0) = (b0 + a0 * b0) + c0).
rewrite commutative.
simpl.
reflexivity.
rewrite H1.
rewrite H2.
rewrite associative.
reflexivity.
Qed.

(*C) f*)
Theorem multAssociative: forall a b c, a * (b * c) = (a * b) * c.
Proof.
intros.
induction a0.
simpl.
reflexivity.
simpl.
rewrite IHa0.
rewrite commutative.
simpl.
rewrite multCommutative.
rewrite commutative.
rewrite multCommutative.
rewrite <- multDistributive.
rewrite multCommutative.
reflexivity.
Qed.

End natProofs.









    