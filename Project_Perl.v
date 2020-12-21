Inductive Var := n | x | y | z.

Scheme Equality for Var.

Definition Env := Var -> nat.

Definition env : Env :=
  fun x =>
    if (Var_eq_dec x n)
    then 10
    else 0.

Definition update (env : Env)
           (x : Var) (v : nat) : Env :=
  fun y =>
    if (Var_eq_dec y x)
    then v
    else (env y).

Notation "S [ X ='  V ]" := (update S X V) (at level 0).

Inductive AExp :=
| avar : Var -> AExp
| anum : nat -> AExp
| aplus : AExp -> AExp -> AExp
| aminus : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp.

Coercion avar : Var >-> AExp.
Coercion anum : nat >-> AExp.

Notation "A +' B" := (aplus A B) (at level 48).
Notation "A -' B" := (aminus A B) (at level 48).
Notation "A *' B" := (amul A B) (at level 46).
Notation "A %' B" := (amod A B) (at level 46).
Notation "A /' B" := (adiv A B) (at level 46).

Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| bequal : AExp -> AExp -> BExp
| blessthan : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp.

Notation "!' A" := (bnot A)(at level 53).
Notation "A == B" := (bequal A B) (at level 51).
Notation "A != B" := (bnot(A == B)) (at level 51).
Notation "A &&' B" := (band A B) (at level 51).
Notation "A ||' B" := (bor A B) (at level 51).
Notation "A <' B" := (blessthan A B) (at level 52).
Notation "A >' B" := (bnot (A <' B)) (at level 52).
Notation "A <=' B" := (bnot (A >' B)) (at level 52).
Notation "A >=' B" := (bnot (A <' B)) (at level 52).



Inductive Coada :=
| nil_coada : Coada
| const_coada : AExp -> Coada -> Coada.

Infix "::" := const_coada (at level 60, right associativity).

Notation "(' ')" := nil_coada.
Notation "(' X ')" := (const_coada X nil_coada).  (* need level *)

Notation "(' x , y , .. , z ')" := (const_coada x (const_coada y .. (const_coada z nil_coada) ..)).

Definition l := (' 2,4,6 ').

Check l.
Compute l.

Definition C_first (l:Coada) : AExp :=
  match l with
    | (' ') => 0
    | v :: _ => v
  end.

Compute (C_first l ).

Definition C_pop (l:Coada) : Coada :=
  match l with
    | (' ') => nil_coada
    | v :: l' => l'
  end.

Compute (C_pop (l)).

Fixpoint append (l1 l2 : Coada) : Coada :=
  match l1 with
  | nil_coada => l2
  | const_coada q l => const_coada q ( append l l2 )
  end.

Definition C_push (n:AExp) (l:Coada) : Coada :=
  match l with
    | (' ') => const_coada n l
    | _ :: _ => append (l) (const_coada n nil_coada)
  end.


Compute (C_push (5) (' 2, 3 ')).

Inductive Stiva :=
| nil_stiva : Stiva
| const_stiva : AExp -> Stiva -> Stiva.

Infix "'::" := const_stiva (at level 60, right associativity).

Notation "{' '}" := nil_stiva.
Notation "{' X '} " := (const_stiva X nil_stiva).

Notation "{' x , y , .. , z  '}" := (const_stiva x (const_stiva y .. (const_stiva z nil_stiva) ..)).


Definition S_pop (l:Stiva) : Stiva :=
  match l with
    | {' '} => nil_stiva
    | v ':: l' => l'
  end.

Definition S_push (n:AExp) (l:Stiva) : Stiva :=
  match l with
    | {' '} => const_stiva n l
    | _ ':: _ => n ':: l
  end.

Compute (S_push (5) {' 2, 3 '}).

Definition S_top (l:Stiva) : AExp :=
  match l with
    | {' '} => 0
    | v ':: _ => v
  end.

Inductive Arr :=
| nil_arr : Arr
| const_arr : AExp -> Arr -> Arr.

Infix "::'" := const_arr (at level 60, right associativity).

Notation "[' ']" := nil_arr.
Notation "[' X '] " := (const_arr X nil_arr).  (* need level *)

Notation "[' x , y , .. , z ']" := (const_arr x (const_arr y .. (const_arr z nil_arr) ..)).

Fixpoint lenght (v:Arr) : AExp :=
  match v with
    | [' '] => 0
    | q ::' v' => 1 +' lenght v'
  end.

Definition v := ['5, 10, 26'].

Compute lenght v.

Fixpoint get (v:Arr) (x:AExp) : AExp :=
  match v with
    | [' '] => 0
    | q ::' w => match x with
                 | 0 => q
                 | _ => get w (x-'1)
                end
  end.


Notation " X [' A '] " := (get X A) (at level 10).

Compute (v [' 0 '] ).

Definition fisier_txt := {' 4, 5, 87, 12, 141, 234, 43 '}.

(*Inductive file :=
  | open_read : file
  | open_write : file
  | close : file.

Notation "open ( A, '<' , B )" := (open_read B) (at level 30).
*)
Inductive H_pair :=
| n_pair : H_pair
| c_pair : nat -> nat -> H_pair.

Inductive Hash :=
| null_h : Hash
| const_h : H_pair -> Hash -> Hash.

Infix ":=:" := c_pair (at level 60, right associativity).

Notation " #( )# " := n_pair.
Notation " #( X , Y )# " := (c_pair X Y)(at level 20).


Infix ":':" := const_h (at level 60, right associativity).

Notation "#' '#" := null_h.
Notation "#' X '#" := (const_h X null_h)(at level 25).

Notation "#' x ; y ; .. ; z '#" := (const_h x (const_h y .. (const_h z null_h) ..)) (at level 25).

Compute #( 2,3 )#.


Definition hash1 := #' #( 2,0 )# '#.
Compute hash1.

Definition hash2 := #' #( 2,5 )# ; #( 3,6 )# '# .

Compute hash2.

Import Nat.

Fixpoint get_h (h:Hash) (k:nat) : nat :=
  match h with
    | null_h => 0
    | q :': w => match q with
                 | n_pair => 0
                 | a :=: b => if ( eqb a k ) 
                              then b
                              else get_h w k
                end
  end.

Notation "H #[ X ]# " := (get_h H X) (at level 30).

Compute get_h hash2 2.

Inductive dec :=
| dcd : Coada -> dec
| dst : Stiva -> dec
| darr : Arr -> dec
| dhs : Hash -> dec.

Coercion dcd : Coada >-> dec.
Coercion dst : Stiva >-> dec.
Coercion darr : Arr >-> dec.
Coercion dhs : Hash >-> dec.

Inductive Stmt :=
| AExpS : AExp -> Stmt
| assignment : Var -> AExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| if_then : BExp -> Stmt -> Stmt
| if_then_else : BExp -> Stmt -> Stmt -> Stmt
| unless : BExp -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| myfor : Stmt -> BExp -> Stmt -> Stmt
| foreach : Stmt -> Stmt -> Stmt
| cd : Coada -> Stmt
| st : Stiva -> Stmt
| arr : Arr -> Stmt
| hs : Hash -> Stmt
| declaration : dec -> Stmt -> Stmt
| sub: Stmt -> Stmt -> Stmt.

Notation "A ::= B" := (assignment A B) (at level 90).
Notation "S ;; S'" := (sequence S S') (at level 93, right associativity).
Notation "A <-: B" := (declaration A B)(at level 90).

Coercion cd : Coada >-> Stmt.
Coercion st : Stiva >-> Stmt.
Coercion arr : Arr >-> Stmt.
Coercion hs : Hash >-> Stmt.
Coercion AExpS : AExp >-> Stmt.



Definition PROGRAM :=
  n::=5;;
  if_then(n == 5) 
  (
    v <-: ['5, 10, 26'];;
    v [' 0 '];;
    S_push (5) {' 2, 3 '};;
    hash1 <-: #' #( 2,5 )# ; #( 3,6 )# '# ;;
    hash1 #[ 3 ]#
  );;
  sub (1) (
    C_push (5) (' 2, 3 ')
);;
  l <-: (' 2,4,6 ');;
  x ::= C_first l;;
  y ::= x +' 5;;
  C_push y l
  .

Check PROGRAM.

























