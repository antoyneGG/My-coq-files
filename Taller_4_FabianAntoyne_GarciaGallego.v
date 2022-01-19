Section LP1.
Variables P Q R S T U: Prop.
(*1*)
(*Si el ejercito marcha contra el enemigo, tiene posibilidades de exito; y
arrasara la capital enemiga, si tiene posibilidades de exito. El ejercito marcha 
contra el enemigo o se repliega rapidamente. Si se repliega rapidamente,
el enemigo atacara su retaguardia; y perdera la guerra, si el enemigo ataca
su retaguardia. Por lo tanto, si no arrasa la capital enemiga, perdera la
guerra.*)

(*P: el ejercito marcha contra el enemigo*)
(*Q: el ejrcito tiene posibilidades de exito*)
(*R: el ejercito arrasara la capital enemiga*)
(*S: el ejercito se repliega rapidamente*)
(*T: el enemigo atacara la retaguardia del ejercito*)
(*U: el ejercito perdera la guerra*)
Hypothesis H0 : P -> Q. 
Hypothesis H1 : Q -> R. 
Hypothesis H2 : P \/ S.
Hypothesis H3 : S -> T.
Hypothesis H4 : T -> U.
Lemma conclusion : ~R -> U.
Proof.
destruct H2.
intro.
apply H5 in H1.
contradiction.
apply H0.
assumption.
intro.
apply H4.
apply H3.
assumption.
Qed.
End LP1.
Section LP2.
(*2*)
(*La fısica describe la naturaleza a base de observables clasicos o a base
de estados abstractos. Si la describe mediante los primeros, entonces nos
permite representar las cosas intuitivamente, pero nos exige renunciar a la
causalidad. En cambio, si la describe mediante los segundos, nos impide
la representacion intuitiva, pero nos permite conservar la causalidad. La
fısica nos permitira representar las cosas intuitivamente, a no ser que nos
exija renunciar a la causalidad. Por lo tanto, no es cierto que nos permita
representar las cosas intuitivamente solo si no renuncia a la causalidad.*)

(*P: La fisica describe la naturaleza a base de observables clasicos*)
(*Q: La fisica describe la naturaleza a base de estados abstractos*)
(*R: La fisica nos permite representar las cosas intuitivamente*)
(*S: La fisica nos permite conservar la causalidad*)
Variables P Q R S T U : Prop.

Hypothesis H0 : P \/ Q.
Hypothesis H1 : (P -> R) /\ ~S.
Hypothesis H2 : (Q -> ~R) /\ S.
Hypothesis H3 : R \/ ~S.
Lemma conclusion2 : ~(~S -> R).
Proof.
intro.
destruct H1.
apply H5.
destruct H3.
destruct H2.
assumption.
destruct H2.
assumption.
Qed.
End LP2.
Section LP3.
(*3*)
(* Si Mariana estaba borracha, entonces Simon es el asesino o Mariana esta
mintiendo. Simon es el asesino o Mariana no estaba borracha y el crimen
ocurrio despues de la media noche. Si el crimen tuvo lugar despues de
la media noche, entonces Simon es el asesino o Mariana Miente. Ademas
sabemos que Mariana no miente cuando esta sobria.*)

(*P: Mariana estaba borracha*)
(*Q: Simon es el asesino*)
(*R: Mariana esta mintiendo*)
(*S: El crimen ocurrio despues de la media noche*)
Variables P Q R S : Prop.
Hypothesis H  : P -> (Q \/ R).
Hypothesis H0 : (Q \/ ~P ) /\ S.
Hypothesis H1 : S -> (Q \/ R).
Hypothesis H2 : ~P -> ~R.
Theorem assassin : Q.
Proof.
destruct H0.
destruct H1.
assumption.
assumption.
destruct H3.
assumption.
destruct H.
apply H2 in H3.
elim H3.
assumption.
assumption.
apply H2 in H3.
elim H3.
assumption.
Qed.
End LP3.
Section LP4.
(*4*)
(*Sabemos que alguien en el equipo consumio drogas. Cuando le preguntamos
a Sam, dijo que Michael o Bill consumieron drogas, pero que no es
posible que los dos. En cambio Michael dijo que o Richard o Sam consumieron 
drogas, pero no ambos. Pero si le preguntamos a Bill, el afirma
que Michael y Matt son los mas probables a consumir drogas, pero no los
dos. Richard por su parte cree que Bill o Matt consumieron drogas, pero
no los dos. Por ultimo, Matt esta seguro que Bill o Richard consumieron
drogas, pero no los dos. Entre todos, Tom es el unico que dice que si
Richard consumio drogas, entonces Bill lo hizo tambien. En conclusion,
Matt o Michael consumieron drogas.*)

(*Q: Michael consumio drogas*)
(*R: Bill consumio drogas*)
(*S: Richard consumio drogas*)
(*T: Sam consumio drogas*)
(*U: Matt consumio drogas*)
Variables Q R S T U : Prop.
Hypothesis H  : Q \/ R \/ S \/ T \/ U.
Hypothesis H1 : (Q /\ ~R) \/ (~Q /\ R).
Hypothesis H2 : (S /\ ~T) \/ (~S /\ T).
Hypothesis H3 : (Q /\ ~U) \/ (~Q /\ U).
Hypothesis H4 : (R /\ ~U) \/ (~R /\ U).
Hypothesis H5 : (R /\ ~S) \/ (~R /\ S).
Hypothesis H6 : S -> R.
Lemma drugs : Q \/ U.
Proof.
destruct H.
left.
assumption.
destruct H0.
destruct H3.
destruct H7.
left.
assumption.
destruct H7.
right.
assumption.
destruct H0.
apply H6 in H0.
destruct H4.
destruct H7.
destruct H1.
destruct H9.
left.
assumption.
destruct H9.
destruct H3.
destruct H11.
left.
assumption.
destruct H11.
right.
assumption.
destruct H7.
right.
assumption.
destruct H0.
destruct H2.
destruct H7.
apply H6 in H7.
destruct H4.
destruct H9.
elim H8.
assumption.
destruct H9.
right.
assumption.
destruct H7.
destruct H4.
destruct H9.
destruct H3.
destruct H11.
left.
assumption.
right.
destruct H11.
assumption.
destruct H9.
right.
assumption.
right.
assumption.
Qed.
End LP4.
Section LP5.
(*5*)
(*Si el euro esta fuerte, el petroleo esta barato pero las exportaciones 
resultan caras. Si Europa se endeuda o la economıa no crece, el petroleo no
estara barato. La economıa crece si y solo si ni las exportaciones resultan
caras ni la inflacion aumenta. Por tanto, si la inflacion aumenta, el euro
no esta fuerte*)

(*P: El euro esta fuerte*)
(*Q: El petroleo esta barato*)
(*R: Las exportaciones resultan caras*)
(*S: Europa se endeuda*)
(*T: La economia crece*)
(*U: La inflacion aumenta*)
Variables P Q R S T U : Prop.
Hypothesis H  : P -> (Q /\ R).
Hypothesis H0 : (S \/ ~T) -> ~Q.
Hypothesis H1 : T <-> (~R /\ ~U).
Theorem euro : U -> ~P.
Proof.
intro.
intro.
destruct H.
assumption.
apply H0.
destruct H1.
destruct H6.
apply H7.
split.
intro.
apply H0.
right.
intro.
apply H1.
assumption.
assumption.
assumption.
intro.
apply H0.
right.
intro.
apply H1.
assumption.
assumption.
assumption.
elim H6.
assumption.
assumption.
Qed.
End LP5.
Section LP6.
(*6*)
(*Un bar tiene las siguientes reglas para sus miembros:
I. Todo miembro que no sea escoces tiene medias.
II. Todo miembro o usa falda o no usa medias.
III. Las personas casadas no van los domingos.
IV. Una persona va el domingo si y solamente si es escoces.
V. Toda persona que usa falda es escoces y esta casado.
VI. Todo escoces usa falda.
Se puede concluir entonces que a este bar no viene nadie*)

(*P: Es escoces*)
(*Q: Tiene medias*)
(*R: Usa falda*)
(*S: Es casado*)
(*T: Va el domingo*)
Variables P Q R S T : Prop.
Hypothesis H  : ~P -> Q.
Hypothesis H0 : R \/ ~Q.
Hypothesis H1 : S -> ~T.
Hypothesis H2 : T <-> P.
Hypothesis H3 : R -> (P /\ S).
Hypothesis H4 : P -> R.
Theorem empty : False.
Proof.
apply H1.    
destruct H3.
destruct H0.
apply H3 in H5.
destruct H5.
apply H4.
assumption.
elim H5.
apply H.
intro.
apply H4 in H6.
apply H3 in H6.
destruct H6.
apply H1.
assumption.
apply H2.
assumption.
assumption.
destruct H0.
apply H3 in H5.
destruct H5.
apply H2.
assumption.
elim H5.
apply H.
intro.
apply H1.
apply H3.
apply H4.
assumption.
apply H2.
assumption.
Qed.
End LP6.





