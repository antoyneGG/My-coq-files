(*punto1*)
Definition punto1 (b1:bool) (b2:bool) : bool := 
    match b1, b2 with
    | _, false => true
    | false, _ => true
    | true, true => false
    end.

Example test1Punto1: (punto1 false false) = true.
Proof. simpl. reflexivity. Qed.
Example test2Punto1: (punto1 false true) = true.
Proof. simpl. reflexivity. Qed.
Example test3Punto1: (punto1 true false) = true.
Proof. simpl. reflexivity. Qed.
Example test4Punto1: (punto1 true true) = false.
Proof. simpl. reflexivity. Qed.

(*definicion de negacion*)
Definition neg (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

(*definicion de conjuncion*)
Definition and (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

(*punto2*)
Definition punto2 (b1:bool) (b2:bool) : bool := (neg (and b1 b2)). 

Compute punto2 true true.

(*punto3*)
Module direccion.
Inductive dir: Type :=
    | cero
    | noventa
    | cientochenta
    | doscientossetenta.

(*punto4*)
Definition punto4 (d1:dir) : dir := 
    match d1 with
    | cero => doscientossetenta
    | noventa => cero
    | cientochenta => noventa
    | doscientossetenta => cientochenta
    end.

Example testPunto4: (punto4 noventa) = cero.
Proof. simpl. reflexivity. Qed.

End direccion.

Check nat.

(*punto5*)
Definition punto5 (n:nat) : nat := 
    match n with
    | O => O
    | S O => O
    | S n => pred n
    end.

Compute (punto5 6).

(*punto6*)
Definition punto6 (f: nat -> nat) (g: nat -> nat) : nat -> nat := fun(x: nat) => f(g x).

Check punto6.

(*punto7*)
Definition punto7 (t: (nat * nat)) : nat :=
  match t with
  | (n1, n2) => n1 + n2
  end.

Compute (punto7 (5, 3)).

(*punto8*)
Definition punto8 (n1:nat) (n2:nat) : nat * nat := ((n1 + n2), (n1 * n2)).

Compute (punto8 10 5).

(*punto9*)
Definition punto9 (g: nat -> nat) (f: nat -> nat -> nat) (n1:nat) (n2:nat) : nat * nat := ((g n2), (f n2 n1)).

Compute (punto9 Nat.div2 Nat.pow 2 4).

(*punto10*)
Definition punto10 (n:nat) : bool := 
  match n with
  | O => false
  | n => (Nat.leb n (Nat.double (Nat.div2 n)))
  end.

Compute (punto10 2).

(*punto11*)
Definition punto11 (n:nat) : nat := 
  match punto10 n with
  | false => n + 1
  | true => Nat.double n
  end.

Compute (punto11 9).

(*punto12*)
Definition punto12 (n1:nat) (n2:nat) (f: nat -> nat) : nat := 
  match Nat.leb n1 n2 with
  | false => f (n1 - n2)
  | true => f (n2 + 1)
  end.

Compute (punto12 2 4 Nat.double).









