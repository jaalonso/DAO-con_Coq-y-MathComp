(* Cap. 1: Funciones y computación *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.

(* =====================================================================
   § 1. Funciones
   ================================================================== *)

(* =====================================================================
   §§ 1.1. Definición de funciones y evaluación de expresiones
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      f : nat -> nat
   tal que (f n) es el sigiente de n. Por ejemplo,
      f 3 == 4.
   ------------------------------------------------------------------ *)

Definition f := fun n => n + 1.

(* ---------------------------------------------------------------------
   Ejercicio. Calcular información sobre la función `f`.
   ------------------------------------------------------------------ *)

About f.

(* Se obtiene
      f : nat -> nat

      f is not universe polymorphic
      Arguments f _%nat_scope
      f is transparent
      Expands to: Constant T1_Computacion.f
 *)

(* ---------------------------------------------------------------------
   Ejercicio. Obtener la definición de `f`.
   ------------------------------------------------------------------ *)

Print f.

(* Se obtiene
      f = addn^~ 1
           : nat -> nat

      Arguments f _%nat_scope
 *)

(* ---------------------------------------------------------------------
   Ejercicio. Obtener información sobre ^~
   ------------------------------------------------------------------ *)

Locate "_ ^~ _".

(* Se obtiene
      Notation "f ^~ y" := (fun x => f x y) : fun_scope (default interpretation)
 *)

(* ---------------------------------------------------------------------
   Ejercicio. Calcular el tipo de `f 3`.
   ------------------------------------------------------------------ *)

Check f 3.

(* Se obtiene
      f 3
           : nat
 *)

(* ---------------------------------------------------------------------
   Ejercicio. Calcular el valor de `f 3`.
   ------------------------------------------------------------------ *)

Eval compute in f 3.

(* Se obtiene
           = 4
           : nat
 *)

(* =====================================================================
   §§ 1.2 Funciones con varios argumentos
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      g : nat -> nat -> nat
   tal que (g n m) es n+m*2. Por ejemplo,
      g 4 5 = 14
   ------------------------------------------------------------------ *)

Definition g (n m : nat) : nat := n + m * 2.

Eval compute in g 4 5.

(* =====================================================================
   §§ 1.3. Funciones de orden superior
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      repeat_twice : (nat -> nat) -> nat -> nat
   tal que (repeat_twice g) es la función obtenida aplicando dos veces
   la función `g`. Por ejemplo,
      repeat_twice f 2 = 4
   ------------------------------------------------------------------ *)

Definition repeat_twice (g : nat -> nat) : nat -> nat :=
  fun x => g (g x).

Eval compute in repeat_twice f 2.

(* =====================================================================
   §§ 1.4. Definiciones locales
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejercicio. Calcular el valor de
      let n := 33 : nat in
      let e := n + n + n in
      e + e + e.
   ------------------------------------------------------------------ *)

Compute
  let n := 33 : nat in
  let e := n + n + n in
  e + e + e.

(* Se obtiene
         = 297
         : nat
*)

(* =====================================================================
   § 2. Tipos de datos
   ================================================================== *)

(* =====================================================================
   §§ 2.1. Valores booleanos
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejercicio. Calcular el tipo de `true`
   ------------------------------------------------------------------ *)

Check true.

(* Se obtiene
      true
           : bool
 *)


(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      f23 : bool -> nat
   tal que (f23 b) es 2 si b es verdadero y 3 en caso contrario. Por
   ejemplo,
      Ejemplos
   ------------------------------------------------------------------ *)

Definition f23 b := if b then 2 else 3.

Eval compute in f23 true.  (* da 2 *)
Eval compute in f23 false. (* da 3*)

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      andb ; bool -> bool -> bool
   tal que (andb b1 b2) es la conjunción de b1 y b2. Por ejemplo,
      andb true false = false
   ------------------------------------------------------------------ *)

Definition andb b1 b2 := if b1 then b2 else false.

Eval compute in andb true false.

(* =====================================================================
   §§ 2.2. Números naturales
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      pred : nat -> nat
   tal que (pred n) es el predecesor de n. Por ejemplo,
      pred 6 = 5
   ------------------------------------------------------------------ *)

Definition pred n := if n is u.+1 then u else n.

Eval compute in pred 6. (* da 5 *)

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      pred5 : nat -> nat
   tal que (pred5 n) es n-5. Por ejemplo,
      pred5 8 = 3
      pred5 4 = 0
   ------------------------------------------------------------------ *)

Definition pred5 n :=
  if n is u.+1.+1.+1.+1.+1 then u else 0.

Eval compute in pred5 8. (* da 3 *)
Eval compute in pred5 4. (* da 0 *)

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      three_patterns : nat -> nat
   tal que (three_patterns) es n-5, si n >= 5, n-1 si n pertenece a
   {1,2,3,4] y 0 en caso contrario. Por ejemplo,
      Ejemplos
   ------------------------------------------------------------------ *)

Definition three_patterns n :=
  match n with
    u.+1.+1.+1.+1.+1 => u
  | v.+1 => v
  | 0 => n
  end.

Eval compute in three_patterns 8. (* da 3 *)
Eval compute in three_patterns 3. (* da 2 *)
Eval compute in three_patterns 0. (* da 0 *)

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      same_bool : bool -> bool -> bool
   tal que (same_bool b1 b2) se verifica si b1 y b2 son iguales. Por
   ejemplo,
   ------------------------------------------------------------------ *)

Definition same_bool b1 b2 :=
  match b1, b2 with
  | true, true => true
  | _, _ => false
  end.

Definition same_bool2 b1 b2 :=
  match b1 with
  | true => match b2 with true => true | _ => false end
  | _ => false
  end.

(* =====================================================================
   §§ 2.3. Recursión sobre los números naturales
   ================================================================== *)

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      addn : nat -> nat -> nat
   tal que (addn n m) es la suma de n y m. Por ejemplo,
      addn 2 3 = 5
   ------------------------------------------------------------------ *)

Fixpoint addn n m :=
  if n is p.+1 then (addn p m).+1 else m.

Fixpoint addn2 n m :=
  match n with
  | 0 => m
  | p.+1 => (addn2 p m).+1
  end.

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      subn : nat -> nat -> nat
   tal que (subn m n) es m menos n. Por ejemplo,
      subn 5 3 = 2
      subn 3 5 = 0
   ------------------------------------------------------------------ *)

Fixpoint subn m n : nat :=
  match m, n with
  | p.+1, q.+1 => subn p q
  | _ , _ => m
  end.

Eval compute in subn 5 3. (* da 2 *)
Eval compute in subn 3 5. (* da 0 *)

(* ---------------------------------------------------------------------
   Ejercicio. Definir la función
      eqn : nat -> nat -> bool
   tal que (eqn m n) que se verifica si m y n son iguales. Por ejemplo,
      eqn 2 2 = true
      eqn 2 3 = false

   Usar la notación `x == y` para `eqn x y`.
   ------------------------------------------------------------------ *)

Fixpoint eqn m n :=
  match m, n with
  | 0, 0 => true
  | p.+1, q.+1 => eqn p q
  | _, _ => false
  end.
Notation "x == y" := (eqn x y).

Eval compute in 2 == 2. (* da true *)
Eval compute in 2 == 3. (* da false *)

Compute 2 == 2. (* da true *)
Compute 2 == 3. (* da false *)

(* =====================================================================
   § 3. Contenedores
   ================================================================== *)

About cons.
Check cons 2 nil.
Check 1 :: 2 :: 3 :: nil.
Check fun l => 1 :: 2 :: 3 :: l.
Definition first_element_or_0 (s : seq nat) :=
  if s is a :: _ then a else 0.

Fixpoint size A (s : seq A) :=
  if s is _ :: tl then (size tl).+1 else 0.
Fixpoint map A B (f : A -> B) s :=
  if s is e :: tl then f e :: map f tl else nil.
Eval compute in [seq i.+1 | i <- [:: 2; 3]].
Check (3, false).
Eval compute in (true, false).1.

Definition only_odd (n : nat) : option nat :=
  if odd n then Some n else None.

Definition ohead (A : Type) (s : seq A) :=
  if s is x :: _ then Some x else None.

(* section *)
Section iterators.
 Variables (T : Type) (A : Type).
 Variables (f : T -> A -> A).
 Implicit Type x : T.
 Fixpoint iter n op x :=
   if n is p.+1 then op (iter p op x) else x.
 Fixpoint foldr a s :=
   if s is x :: xs then f x (foldr a xs) else a.
 About foldr.
 Variable init : A.
 Variables x1 x2 x3 : T.
  Eval compute in foldr init [:: x1; x2; x3].
End iterators.
About iter.
About foldr.
Eval compute in iter 5 pred 7.
Eval compute in foldr addn 0 [:: 1; 2; 3].
Fixpoint addn_alt m n := if m is u.+1 then addn_alt u n.+1 else n.
Section symbolic.
  Variable n : nat.
  Eval simpl in pred (addn_alt n.+1 7).
  Eval simpl in pred (addn n.+1 7).
End symbolic.

(* iterated ops *)
Fixpoint iota m n := if n is u.+1 then m :: iota m.+1 u else [::].
Notation "\sum_ ( m <= i < n ) F" :=
  (foldr (fun i a => F + a) 0 (iota m (n-m))).
Eval compute in \sum_( 1 <= i < 5 ) (i * 2 - 1).
Eval compute in \sum_( 1 <= i < 5 ) i.

(* aggregated data *)
Record point := Point { x : nat; y : nat; z : nat }.
Eval compute in x (Point 3 0 2).
Eval compute in y (Point 3 0 2).

(** Exercises *************************************** *)

Module exercises.
(* pair *)




Eval compute in fst (4,5).

(* iter add *)
Definition addn n1 n2 := iter n1 S n2.

Eval compute in addn 3 4.

(* iter mul *)
Definition muln n1 n2 := iter n1 (addn n2) 0.

Eval compute in muln 3 4.

(* nth *)
Fixpoint nth T (def : T) (s : seq T) n :=
  if s is x :: s' then if n is n'.+1 then nth def s' n' else x else def.

Eval compute in nth 0 [:: 3; 7; 11; 22] 2.
Eval compute in nth 0 [:: 3; 7; 11; 22] 7.

(* rev *)
Fixpoint catrev T (s1 s2 : seq T) :=
  if s1 is x :: xs then catrev xs (x :: s2) else s2.

Definition rev T (s : seq T) := catrev s [::].

Eval compute in rev [:: 1; 2; 3].

(* flatten *)
Definition flatten T (s : seq (seq T)) := foldr cat [::] s.

Eval compute in
  flatten [:: [:: 1; 2; 3]; [:: 4; 5] ].

(* all_words *)
Definition all_words n T (alphabet : seq T) :=
  let prepend x wl := [seq x :: w | w <- wl] in
  let extend wl := flatten [seq prepend x wl | x <- alphabet] in
  iter n extend [::[::]].

Eval compute in all_words 2 [:: 1; 2; 3].

End exercises.
