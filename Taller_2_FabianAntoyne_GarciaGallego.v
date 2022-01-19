(*Definicion de LP*)
Inductive LP: Type := 
  | T
  | F
  | var
  | neg (F1: LP)
  | dis (F1: LP) (F2: LP)
  | con (F1: LP) (F2: LP)
  | imp (F1: LP) (F2: LP).

Compute dis. 

(*Parentesis*)
Fixpoint parentesis (alpha: LP): nat :=
    match alpha with
    | T => 0
    | F => 0
    | var => 0
    | neg F1 => 2 + parentesis(F1)
    | dis F1 F2 => 2 + parentesis(F1) + parentesis(F2)
    | con F1 F2 => 2 + parentesis(F1) + parentesis(F2)
    | imp F1 F2 => 2 + parentesis(F1) + parentesis(F2)
    end.

Compute parentesis (dis (con (neg (var)) (var)) (imp (var) (var))).

(*Negacion*)
Fixpoint negacion (alpha: LP): nat :=
    match alpha with
    | T => 0
    | F => 0
    | var => 0
    | neg F1 => 1 + negacion(F1)
    | dis F1 F2 => negacion(F1) + negacion(F2)
    | con F1 F2 => negacion(F1) + negacion(F2)
    | imp F1 F2 => negacion(F1) + negacion(F2)
    end.

Compute negacion (con (neg (T)) (neg (T))).

(*Variables*)
Fixpoint variables (alpha: LP): nat :=
    match alpha with
    | T => 1
    | F => 1
    | var => 1
    | neg F1 => variables(F1)
    | dis F1 F2 => variables(F1) + variables(F2)
    | con F1 F2 => variables(F1) + variables(F2)
    | imp F1 F2 => variables(F1) + variables(F2)
    end.

Compute variables (imp (neg (T)) (dis (T) (F))).

Notation "~ p" := (neg (p)).
Notation "p && q" := (con (p) (q)).
Notation "p || q" := (dis (p) (q)).
Notation "p -> q" := (imp (p) (q)).

Compute parentesis ((T && F) && ~ (T -> F)).



(*Definicion de arbol binario*)
Inductive Tree: Type :=
    | nil
    | leave (n: nat)
    | branch (n: nat) (l1: Tree) (l2: Tree).

(*Suma arbol*)
Fixpoint suma (t: Tree): nat :=
    match t with
    | nil => 0
    | leave n => n
    | branch n l1 l2 => n + suma(l1) + suma(l2)
    end.

Compute suma (branch (5) (branch (3) (leave (1)) (leave (1))) (leave (4))).

(*Contar nodos*)
Fixpoint contNodos (t: Tree): nat :=
    match t with
    | nil => 0
    | leave n => 1
    | branch n l1 l2 => 1 + contNodos(l1) + contNodos(l2)
    end.

Compute contNodos (branch (5) (branch (3) (leave (1)) (leave (1))) (leave (4))).

(*Arbol horizontal*)
Fixpoint refHorizontal (t: Tree): Tree :=
    match t with
    | nil => t
    | leave n => t
    | branch n l1 l2 => branch n (refHorizontal(l2)) (refHorizontal(l1))
    end.

Compute refHorizontal (branch (5) (branch (3) (leave (1)) (leave (2))) (leave (4))).

(*Potencia*)
Fixpoint potencia (n1: nat) (n2: nat): nat :=
    match n1, n2 with
    | _, O => 1
    | O, _ => 0
    | S a, S b => n1 * (potencia (n1) (b))
    end.

Compute potencia 0 5.

(*Igualdad*)
Fixpoint igualdad (n1: nat) (n2:nat): Prop :=
    match n1, n2 with
    | O, O => True
    | O, _ => False
    | _, O => False
    | S a, S b => igualdad (a) (b)
    end.

Compute igualdad 5 5.

(*Resta*)
Fixpoint resta (n1: nat) (n2: nat): nat :=
    match n1, n2 with
    | O, O => 0
    | _, O => n1
    | O, _ => 0
    | S a, S b => resta a b
    end.

Compute resta 112 100.
