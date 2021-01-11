Inductive Var := n | x | y | z | s | k.

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

Require Import Coq.Arith.PeanoNat.

Fixpoint aevalF (a : AExp) (env : Env) : nat :=
  match a with
  | avar var => env var
  | anum v => v
  | aplus a1 a2 => (aevalF a1 env) + (aevalF a2 env)
  | aminus a1 a2 => (aevalF a1 env) - (aevalF a2 env)
  | amul a1 a2 => (aevalF a1 env) * (aevalF a2 env)
  | adiv a1 a2 => (aevalF a1 env) / (aevalF a2 env)
  | amod a1 a2 => (aevalF a1 env) mod (aevalF a2 env)
  end.

Inductive Coada :=
| nil_coada : Coada
| const_coada : AExp -> Coada -> Coada.

Infix "::" := const_coada (at level 60, right associativity).

Notation "(' ')" := nil_coada.
Notation "(' X ')" := (const_coada X nil_coada).  (* need level *)

Notation "(' x , y , .. , z ')" := (const_coada x (const_coada y .. (const_coada z nil_coada) ..)).

Definition l1 := (' 2,4,6 ').
Definition l2 := (' 2, 23, 38 ').

Check l2.
Compute l2.

Definition C_first (l:Coada) : AExp :=
  match l with
    | (' ') => 0
    | v :: _ => v
  end.

Compute (C_first l1 ).

Definition C_pop (l:Coada) : Coada :=
  match l with
    | (' ') => nil_coada
    | v :: l' => l'
  end.

Compute (C_pop (l1)).

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

Definition stv1 := {' 5,6 '}.

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
| c_pair : nat -> AExp -> H_pair.

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



Fixpoint get_h (h:Hash) (k:nat) : AExp :=
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



Reserved Notation "A =[ S ]=> N" (at level 60).

Inductive aeval : AExp -> Env -> nat -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> n  
| var : forall v sigma, avar v =[ sigma ]=> (sigma v)
| add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 + i2 ->
    a1 +' a2 =[sigma]=> n
| subst : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 - i2 ->
    a1 -' a2 =[sigma]=> n
| times : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 * i2 ->
    a1 *' a2 =[sigma]=> n
| div : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 / i2 ->
    a1 /' a2 =[sigma]=> n
| modulo : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 mod i2 ->
    a1 %' a2 =[sigma]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).

Hint Constructors aeval.

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

Fixpoint bevalF (b : BExp) (env : Env) : bool :=
  match b with
  | btrue => true
  | bfalse => false
  | bequal a1 a2 => Nat.eqb (aevalF a1 env) (aevalF a2 env)
  | blessthan a1 a2 => Nat.leb (aevalF a1 env) (aevalF a2 env)
  | bnot b' => negb (bevalF b' env)
  | band b1 b2 => andb (bevalF b1 env) (bevalF b2 env)
  | bor b1 b2 => orb (bevalF b1 env) (bevalF b2 env)
  end.

Reserved Notation "B ={ S }=> B'" (at level 70).

Inductive beval : BExp -> Env -> bool -> Prop :=
| e_true : forall sigma, btrue ={ sigma }=> true
| e_false : forall sigma, bfalse ={ sigma }=> false
| e_equal : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = Nat.eqb i1 i2 ->
    a1 == a2 ={ sigma }=> b
| e_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = Nat.leb i1 i2 ->
    a1 <=' a2 ={ sigma }=> b
| e_nottrue : forall b sigma,
    b ={ sigma }=> true ->
    (bnot b) ={ sigma }=> false
| e_notfalse : forall b sigma,
    b ={ sigma }=> false ->
    (bnot b) ={ sigma }=> true
| e_andtrue : forall b1 b2 sigma true,
    b1 ={ sigma }=> true ->
    b2 ={ sigma }=> true ->
    band b1 b2 ={ sigma }=> true
| e_andfalse : forall b1 b2 sigma,
    b1 ={ sigma }=> false ->
    band b1 b2 ={ sigma }=> false 
| e_ortrue : forall b1 b2 sigma,
    b1 ={ sigma }=> true ->
    bor b1 b2 ={ sigma }=> true
| e_orfalse : forall b1 b2 sigma,
    b1 ={ sigma }=> false ->
    b2 ={ sigma }=> false ->
    bor b1 b2 ={ sigma }=> false 
where "B ={ S }=> B'" := (beval B S B').


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
| assignment : Var -> AExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| if_then : BExp -> Stmt -> Stmt
| if_then_else : BExp -> Stmt -> Stmt -> Stmt
| unless : BExp -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| cd : Coada -> Stmt
| st : Stiva -> Stmt
| arr : Arr -> Stmt
| hs : Hash -> Stmt
| declaration : dec -> Stmt -> Stmt
| sub: nat -> Stmt -> Stmt.

Notation "A ::= B" := (assignment A B) (at level 90).
Notation "S ;; S'" := (sequence S S') (at level 93, right associativity).
Notation "A <-: B" := (declaration A B)(at level 90).

Coercion cd : Coada >-> Stmt.
Coercion st : Stiva >-> Stmt.
Coercion arr : Arr >-> Stmt.
Coercion hs : Hash >-> Stmt.

Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).
Check update.
Inductive eval : Stmt -> Env -> Env -> Prop :=
| e_assignment: forall a i x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x i) ->
    (x ::= a) -{ sigma }-> sigma'
| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;; s2) -{ sigma }-> sigma2
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    while b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    (s ;; while b s) -{ sigma }-> sigma' ->
    while b s -{ sigma }-> sigma'
| e_if_false : forall b s s' sigma,
    b ={ sigma }=> false ->
    if_then_else b s s' -{ sigma }-> sigma
| e_if_true : forall b s s' sigma ,
    b ={ sigma }=> true ->
    if_then_else b s s' -{ sigma }-> sigma
| e_ift_true : forall b s sigma ,
    b ={ sigma }=> true ->
    if_then b s -{ sigma }-> sigma
| e_sub: forall n s sigma,
    sub n s -{ sigma }-> sigma
| e_decl: forall dec s sigma,
    declaration dec s -{ sigma }-> sigma
| e_cpush: forall n l sigma,
    C_push n l -{ sigma }-> sigma



where "s -{ sigma }-> sigma'" := (eval s sigma sigma').


Definition PROGRAM :=
  n::=5;;
  if_then(n == 5) 
  (
    v <-: ['5, 10, 26'];;
    x ::= v [' 0 '];;
    stv1 <-: {' 2,3 '};;
    S_push (5) stv1;;
    hash1 <-: #' #( 2,5 )# ; #( 3,6 )# '# ;;
    y ::= hash1 #[ 3 ]#
  );;

  sub (1) (
     l1 <-:(' 2, 3 ');;
     C_push (10) l1
);;
  l2 <-: (' 2, 23, 38 ');;
  s ::= C_first l2;;
  k ::= s +' 5;;
  C_push k l2
  .

Check PROGRAM.

Fixpoint execute (s : Stmt) (env : Env) (gas : nat) : Env :=
  match gas with
  | 0 => env
  | S gas' =>   match s with
                | assignment v aexp => update env v (aevalF aexp env)
                | sequence S1 S2 => execute S2 (execute S1 env gas') gas'
                | if_then cond s' => if (bevalF cond env )
                       then execute (s') env gas'
                       else env
                | if_then_else cond s1 s2 => if (bevalF cond env )
                            then execute (s1) env gas'
                            else execute (s2) env gas'
                | unless cond s' => if (bevalF cond env)
                                   then execute (s') env gas'
                                   else env
                | while cond s' => if (bevalF cond env)
                                   then execute (s' ;; (while cond s')) env gas'
                                   else env
                | cd Coada => env
                | st Stiva => env
                | arr Arr => env
                | hs Hash => env
                | declaration A B => env
                | sub s1 s2 => execute s2 env gas'
                end
  end.

Definition env0 := fun (var : Var) => 0.

Compute (execute PROGRAM env0) 100 k.

Definition state0 := fun (x : Var) => 0.

Example eval_program :
  exists state, PROGRAM -{ state0 }-> state /\ state k = 7.
Proof.
  eexists.
  split.
  -unfold PROGRAM.
    + eapply e_seq.
     ++ eapply e_assignment; eauto.
     ++ eapply e_seq.
      +++ eapply e_ift_true.
        ++++ eapply e_equal; eauto.
      +++ eapply e_seq.
        ++++ eapply e_sub.
        ++++ eapply e_seq.
          +++++ eapply e_decl.
          +++++ eapply e_seq.
            ++++++ eapply e_assignment; eauto.
                   eapply const.
            ++++++ eapply e_seq.
            +++++++ eapply e_assignment; eauto.
            +++++++ eapply e_cpush.
  -simpl. unfold update. simpl. reflexivity.
Qed.




























