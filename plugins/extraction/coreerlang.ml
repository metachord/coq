open Pp
open Util
open Names
open Libnames
open Miniml
open Mlutil
open Common
open Table
open Str

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| y :: l' -> succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, p) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| ExistT (x0, h) -> h

(** val plus : int -> int -> int **)

let rec plus = (+)

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x :: l' -> app (rev l') (x :: [])

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t -> f b (fold_right f a0 t)

(** val int_of_nat : int -> int **)

let int_of_nat =
  let rec loop acc n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      acc)
      (fun n0 ->
      loop (succ acc) n0)
      n
  in loop 0

module CoreErlang = 
 struct 
  type atom_t =
    string
    (* singleton inductive, whose constructor was mk_atom *)
  
  (** val atom_t_rect : (string -> 'a1) -> atom_t -> 'a1 **)
  
  let atom_t_rect f a =
    f a
  
  (** val atom_t_rec : (string -> 'a1) -> atom_t -> 'a1 **)
  
  let atom_t_rec f a =
    f a
  
  (** val atom_eq_dec_obligation_1 :
      atom_t -> char list -> string -> bool **)
  
  let atom_eq_dec_obligation_1 a s s' =
    true
  
  (** val atom_eq_dec_obligation_2 :
      atom_t -> char list -> string -> bool **)
  
  let atom_eq_dec_obligation_2 a s s' =
    false
  
  (** val atom_eq_dec : atom_t -> char list -> bool **)
  
  let atom_eq_dec a s =
    if (function a -> function b -> a = b) a
         ((function s ->
     let r = String.create (List.length s) in
     let rec fill pos = function
       | [] -> r
       | c :: s -> r.[pos] <- c; fill (pos + 1) s
     in fill 0 s)
           s)
    then atom_eq_dec_obligation_1 a s a
    else atom_eq_dec_obligation_2 a s a
  
  type integer_t = int
  
  type char_t = char
  
  type module_t =
  | Coq_module of atom_t * fname_t list * attr_t list * def_t list
  and fname_t =
  | Coq_fname of atom_t * int
  and attr_t =
  | Coq_attr of atom_t * const_t
  and const_t =
  | Coq_const of lit_t * const_t list
  and lit_t =
  | Coq_lit_int of integer_t
  | Coq_lit_atom of atom_t
  | Coq_lit_char of char_t
  | Coq_lit_str of string
  | Coq_lit_nil
  | Coq_lit_cons of atom_t
  | Coq_lit_tup
  and def_t =
  | Coq_def of fname_t * fun_t
  | Coq_def_custom of string * string
  and fun_t =
  | Coq_func of var_t list * term_t
  and var_t =
  | Coq_var of string
  | Coq_var_atom of string
  and term_t =
  | Coq_term_var of var_t
  | Coq_term_fname of fname_t
  | Coq_term_lit of lit_t * term_t list
  | Coq_term_fun of fun_t
  | Coq_term_let of var_t * term_t * term_t
  | Coq_term_case of term_t * clause_t list
  | Coq_term_letrec of def_t list * term_t
  | Coq_term_apply of term_t * term_t list
  | Coq_term_call of term_t * term_t * term_t list
  | Coq_term_primop of atom_t * term_t list
  | Coq_term_try of term_t * var_t list * term_t * var_t list * term_t
  | Coq_term_recv of clause_t list * term_t * term_t
  | Coq_term_do of term_t * term_t
  | Coq_term_catch of term_t
  | Coq_term_globl of atom_t
  | Coq_term_custom of string
  and clause_t =
  | Coq_clause of pat_t * term_t * term_t
  and pat_t =
  | Coq_pat_var of var_t
  | Coq_pat_lit of lit_t * pat_t list
  | Coq_pat_alias of var_t * pat_t
  
  (** val module_t_rect :
      (atom_t -> fname_t list -> attr_t list -> def_t list -> 'a1) ->
      module_t -> 'a1 **)
  
  let module_t_rect f = function
  | Coq_module (x, x0, x1, x2) -> f x x0 x1 x2
  
  (** val module_t_rec :
      (atom_t -> fname_t list -> attr_t list -> def_t list -> 'a1) ->
      module_t -> 'a1 **)
  
  let module_t_rec f = function
  | Coq_module (x, x0, x1, x2) -> f x x0 x1 x2
  
  (** val fname_t_rect : (atom_t -> int -> 'a1) -> fname_t -> 'a1 **)
  
  let fname_t_rect f = function
  | Coq_fname (x, x0) -> f x x0
  
  (** val fname_t_rec : (atom_t -> int -> 'a1) -> fname_t -> 'a1 **)
  
  let fname_t_rec f = function
  | Coq_fname (x, x0) -> f x x0
  
  (** val attr_t_rect : (atom_t -> const_t -> 'a1) -> attr_t -> 'a1 **)
  
  let attr_t_rect f = function
  | Coq_attr (x, x0) -> f x x0
  
  (** val attr_t_rec : (atom_t -> const_t -> 'a1) -> attr_t -> 'a1 **)
  
  let attr_t_rec f = function
  | Coq_attr (x, x0) -> f x x0
  
  (** val const_t_rect : (lit_t -> const_t list -> 'a1) -> const_t -> 'a1 **)
  
  let const_t_rect f = function
  | Coq_const (x, x0) -> f x x0
  
  (** val const_t_rec : (lit_t -> const_t list -> 'a1) -> const_t -> 'a1 **)
  
  let const_t_rec f = function
  | Coq_const (x, x0) -> f x x0
  
  (** val lit_t_rect :
      (integer_t -> 'a1) -> (atom_t -> 'a1) -> (char_t -> 'a1) -> (string ->
      'a1) -> 'a1 -> (atom_t -> 'a1) -> 'a1 -> lit_t -> 'a1 **)
  
  let lit_t_rect f f0 f1 f2 f3 f4 f5 = function
  | Coq_lit_int x -> f x
  | Coq_lit_atom x -> f0 x
  | Coq_lit_char x -> f1 x
  | Coq_lit_str x -> f2 x
  | Coq_lit_nil -> f3
  | Coq_lit_cons x -> f4 x
  | Coq_lit_tup -> f5
  
  (** val lit_t_rec :
      (integer_t -> 'a1) -> (atom_t -> 'a1) -> (char_t -> 'a1) -> (string ->
      'a1) -> 'a1 -> (atom_t -> 'a1) -> 'a1 -> lit_t -> 'a1 **)
  
  let lit_t_rec f f0 f1 f2 f3 f4 f5 = function
  | Coq_lit_int x -> f x
  | Coq_lit_atom x -> f0 x
  | Coq_lit_char x -> f1 x
  | Coq_lit_str x -> f2 x
  | Coq_lit_nil -> f3
  | Coq_lit_cons x -> f4 x
  | Coq_lit_tup -> f5
  
  (** val def_t_rect :
      (fname_t -> fun_t -> 'a1) -> (string -> string -> 'a1) -> def_t -> 'a1 **)
  
  let def_t_rect f f0 = function
  | Coq_def (x, x0) -> f x x0
  | Coq_def_custom (x, x0) -> f0 x x0
  
  (** val def_t_rec :
      (fname_t -> fun_t -> 'a1) -> (string -> string -> 'a1) -> def_t -> 'a1 **)
  
  let def_t_rec f f0 = function
  | Coq_def (x, x0) -> f x x0
  | Coq_def_custom (x, x0) -> f0 x x0
  
  (** val fun_t_rect : (var_t list -> term_t -> 'a1) -> fun_t -> 'a1 **)
  
  let fun_t_rect f = function
  | Coq_func (x, x0) -> f x x0
  
  (** val fun_t_rec : (var_t list -> term_t -> 'a1) -> fun_t -> 'a1 **)
  
  let fun_t_rec f = function
  | Coq_func (x, x0) -> f x x0
  
  (** val var_t_rect : (string -> 'a1) -> (string -> 'a1) -> var_t -> 'a1 **)
  
  let var_t_rect f f0 = function
  | Coq_var x -> f x
  | Coq_var_atom x -> f0 x
  
  (** val var_t_rec : (string -> 'a1) -> (string -> 'a1) -> var_t -> 'a1 **)
  
  let var_t_rec f f0 = function
  | Coq_var x -> f x
  | Coq_var_atom x -> f0 x
  
  (** val term_t_rect :
      (var_t -> 'a1) -> (fname_t -> 'a1) -> (lit_t -> term_t list -> 'a1) ->
      (fun_t -> 'a1) -> (var_t -> term_t -> 'a1 -> term_t -> 'a1 -> 'a1) ->
      (term_t -> 'a1 -> clause_t list -> 'a1) -> (def_t list -> term_t -> 'a1
      -> 'a1) -> (term_t -> 'a1 -> term_t list -> 'a1) -> (term_t -> 'a1 ->
      term_t -> 'a1 -> term_t list -> 'a1) -> (atom_t -> term_t list -> 'a1)
      -> (term_t -> 'a1 -> var_t list -> term_t -> 'a1 -> var_t list ->
      term_t -> 'a1 -> 'a1) -> (clause_t list -> term_t -> 'a1 -> term_t ->
      'a1 -> 'a1) -> (term_t -> 'a1 -> term_t -> 'a1 -> 'a1) -> (term_t ->
      'a1 -> 'a1) -> (atom_t -> 'a1) -> (string -> 'a1) -> term_t -> 'a1 **)
  
  let rec term_t_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 = function
  | Coq_term_var v -> f v
  | Coq_term_fname f15 -> f0 f15
  | Coq_term_lit (l, l0) -> f1 l l0
  | Coq_term_fun f15 -> f2 f15
  | Coq_term_let (v, t0, t1) ->
    f3 v t0
      (term_t_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t0) t1
      (term_t_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t1)
  | Coq_term_case (t0, l) ->
    f4 t0
      (term_t_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t0) l
  | Coq_term_letrec (l, t0) ->
    f5 l t0
      (term_t_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t0)
  | Coq_term_apply (t0, l) ->
    f6 t0
      (term_t_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t0) l
  | Coq_term_call (t0, t1, l) ->
    f7 t0
      (term_t_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t0) t1
      (term_t_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t1) l
  | Coq_term_primop (a, l) -> f8 a l
  | Coq_term_try (t0, l, t1, l0, t2) ->
    f9 t0
      (term_t_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t0) l
      t1 (term_t_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t1)
      l0 t2
      (term_t_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t2)
  | Coq_term_recv (l, t0, t1) ->
    f10 l t0
      (term_t_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t0) t1
      (term_t_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t1)
  | Coq_term_do (t0, t1) ->
    f11 t0
      (term_t_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t0) t1
      (term_t_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t1)
  | Coq_term_catch t0 ->
    f12 t0
      (term_t_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t0)
  | Coq_term_globl a -> f13 a
  | Coq_term_custom c -> f14 c
  
  (** val term_t_rec :
      (var_t -> 'a1) -> (fname_t -> 'a1) -> (lit_t -> term_t list -> 'a1) ->
      (fun_t -> 'a1) -> (var_t -> term_t -> 'a1 -> term_t -> 'a1 -> 'a1) ->
      (term_t -> 'a1 -> clause_t list -> 'a1) -> (def_t list -> term_t -> 'a1
      -> 'a1) -> (term_t -> 'a1 -> term_t list -> 'a1) -> (term_t -> 'a1 ->
      term_t -> 'a1 -> term_t list -> 'a1) -> (atom_t -> term_t list -> 'a1)
      -> (term_t -> 'a1 -> var_t list -> term_t -> 'a1 -> var_t list ->
      term_t -> 'a1 -> 'a1) -> (clause_t list -> term_t -> 'a1 -> term_t ->
      'a1 -> 'a1) -> (term_t -> 'a1 -> term_t -> 'a1 -> 'a1) -> (term_t ->
      'a1 -> 'a1) -> (atom_t -> 'a1) -> (string -> 'a1) -> term_t -> 'a1 **)
  
  let rec term_t_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 = function
  | Coq_term_var v -> f v
  | Coq_term_fname f15 -> f0 f15
  | Coq_term_lit (l, l0) -> f1 l l0
  | Coq_term_fun f15 -> f2 f15
  | Coq_term_let (v, t0, t1) ->
    f3 v t0
      (term_t_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t0) t1
      (term_t_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t1)
  | Coq_term_case (t0, l) ->
    f4 t0 (term_t_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t0)
      l
  | Coq_term_letrec (l, t0) ->
    f5 l t0
      (term_t_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t0)
  | Coq_term_apply (t0, l) ->
    f6 t0 (term_t_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t0)
      l
  | Coq_term_call (t0, t1, l) ->
    f7 t0 (term_t_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t0)
      t1 (term_t_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t1)
      l
  | Coq_term_primop (a, l) -> f8 a l
  | Coq_term_try (t0, l, t1, l0, t2) ->
    f9 t0 (term_t_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t0)
      l t1
      (term_t_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t1) l0
      t2 (term_t_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t2)
  | Coq_term_recv (l, t0, t1) ->
    f10 l t0
      (term_t_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t0) t1
      (term_t_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t1)
  | Coq_term_do (t0, t1) ->
    f11 t0
      (term_t_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t0) t1
      (term_t_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t1)
  | Coq_term_catch t0 ->
    f12 t0
      (term_t_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 t0)
  | Coq_term_globl a -> f13 a
  | Coq_term_custom c -> f14 c
  
  (** val clause_t_rect :
      (pat_t -> term_t -> term_t -> 'a1) -> clause_t -> 'a1 **)
  
  let clause_t_rect f = function
  | Coq_clause (x, x0, x1) -> f x x0 x1
  
  (** val clause_t_rec :
      (pat_t -> term_t -> term_t -> 'a1) -> clause_t -> 'a1 **)
  
  let clause_t_rec f = function
  | Coq_clause (x, x0, x1) -> f x x0 x1
  
  (** val pat_t_rect :
      (var_t -> 'a1) -> (lit_t -> pat_t list -> 'a1) -> (var_t -> pat_t ->
      'a1 -> 'a1) -> pat_t -> 'a1 **)
  
  let rec pat_t_rect f f0 f1 = function
  | Coq_pat_var v -> f v
  | Coq_pat_lit (l, l0) -> f0 l l0
  | Coq_pat_alias (v, p0) -> f1 v p0 (pat_t_rect f f0 f1 p0)
  
  (** val pat_t_rec :
      (var_t -> 'a1) -> (lit_t -> pat_t list -> 'a1) -> (var_t -> pat_t ->
      'a1 -> 'a1) -> pat_t -> 'a1 **)
  
  let rec pat_t_rec f f0 f1 = function
  | Coq_pat_var v -> f v
  | Coq_pat_lit (l, l0) -> f0 l l0
  | Coq_pat_alias (v, p0) -> f1 v p0 (pat_t_rec f f0 f1 p0)
 end

(** val pp_global : Kind -> Libnames.global_reference -> string **)

let pp_global k r =
  if is_inline_custom r then find_custom r else pp_global k r

(** val mk_idset : char list list -> idset **)

let mk_idset ss =
  fold_right (fun s ->
    Idset.add
      (id_of_string
        ((function s ->
     let r = String.create (List.length s) in
     let rec fill pos = function
       | [] -> r
       | c :: s -> r.[pos] <- c; fill (pos + 1) s
     in fill 0 s)
          s))) Idset.empty ss

(** val keywords0 : idset **)

let keywords0 =
  mk_idset
    (('a'::('f'::('t'::('e'::('r'::[]))))) :: (('a'::('p'::('p'::('l'::('y'::[]))))) :: (('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::[])))))))))) :: (('c'::('a'::('l'::('l'::[])))) :: (('c'::('a'::('s'::('e'::[])))) :: (('c'::('a'::('t'::('c'::('h'::[]))))) :: (('d'::('o'::[])) :: (('e'::('n'::('d'::[]))) :: (('f'::('u'::('n'::[]))) :: (('i'::('n'::[])) :: (('l'::('e'::('t'::[]))) :: (('l'::('e'::('t'::('r'::('e'::('c'::[])))))) :: (('m'::('o'::('d'::('u'::('l'::('e'::[])))))) :: (('o'::('f'::[])) :: (('p'::('r'::('i'::('m'::('o'::('p'::[])))))) :: (('r'::('e'::('c'::('e'::('i'::('v'::('e'::[]))))))) :: (('t'::('r'::('y'::[]))) :: (('w'::('h'::('e'::('n'::[])))) :: (('_'::('w'::('c'::[]))) :: [])))))))))))))))))))

(** val file_suffix0 : string **)

let file_suffix0 =
  (function s ->
     let r = String.create (List.length s) in
     let rec fill pos = function
       | [] -> r
       | c :: s -> r.[pos] <- c; fill (pos + 1) s
     in fill 0 s)
    ('.'::('c'::('o'::('r'::('e'::[])))))

(** val sig_suffix0 : string option **)

let sig_suffix0 =
  Some
    ((function s ->
     let r = String.create (List.length s) in
     let rec fill pos = function
       | [] -> r
       | c :: s -> r.[pos] <- c; fill (pos + 1) s
     in fill 0 s)
      ('.'::('h'::('r'::('l'::[])))))

(** val map2 : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list **)

let rec map2 f xs ys =
  match xs with
  | [] -> []
  | x :: xs' ->
    (match ys with
     | [] -> []
     | y :: ys' -> (f x y) :: (map2 f xs' ys'))

(** val map3 :
    ('a1 -> 'a2 -> 'a3 -> 'a4) -> 'a1 list -> 'a2 list -> 'a3 list -> 'a4
    list **)

let rec map3 f xs ys zs =
  match xs with
  | [] -> []
  | x :: xs' ->
    (match ys with
     | [] -> []
     | y :: ys' ->
       (match zs with
        | [] -> []
        | z :: zs' -> (f x y z) :: (map3 f xs' ys' zs')))

(** val extr_pat :
    Common.env -> Miniml.ml_pattern -> Names.identifier list ->
    CoreErlang.pat_t **)

let rec extr_pat e p ids =
  match p with
  | Miniml.Pcons (r, xs) ->
    CoreErlang.Coq_pat_lit ((CoreErlang.Coq_lit_cons (pp_global Cons r)),
      (map (fun x -> extr_pat e x ids) xs))
  | Miniml.Ptuple xs ->
    CoreErlang.Coq_pat_lit (CoreErlang.Coq_lit_tup,
      (map (fun x -> extr_pat e x ids) xs))
  | Miniml.Prel k ->
    CoreErlang.Coq_pat_var (CoreErlang.Coq_var
      (string_of_id (get_db_name k e)))
  | Miniml.Pwild ->
    CoreErlang.Coq_pat_var (CoreErlang.Coq_var
      ((function s ->
     let r = String.create (List.length s) in
     let rec fill pos = function
       | [] -> r
       | c :: s -> r.[pos] <- c; fill (pos + 1) s
     in fill 0 s)
        ('_'::('w'::('c'::[])))))
  | Miniml.Pusual k ->
    CoreErlang.Coq_pat_lit ((CoreErlang.Coq_lit_cons (pp_global Cons k)),
      (map (fun i -> CoreErlang.Coq_pat_var (CoreErlang.Coq_var
        (string_of_id i))) ids))

(** val extr_ast_func :
    (Common.env, Miniml.ml_ast) sigT -> CoreErlang.term_t **)

let rec extr_ast_func x =
  let e = projT1 x in
  let t = projT2 x in
  let extr_ast0 = fun e0 t0 -> let y = ExistT (e0, t0) in extr_ast_func y in
  (match t with
   | Miniml.MLrel k ->
     CoreErlang.Coq_term_var (CoreErlang.Coq_var
       (string_of_id (get_db_name k e)))
   | Miniml.MLapp (f, xs) ->
     (match f with
      | Miniml.MLglob r ->
        let r_modpath = string_of_mp (modpath_of_r r) in
        let r' = pp_global Term r in
        let filtered_var =
          Str.split
            (Str.regexp
              ((function s ->
     let r = String.create (List.length s) in
     let rec fill pos = function
       | [] -> r
       | c :: s -> r.[pos] <- c; fill (pos + 1) s
     in fill 0 s)
                ('['::('~'::(']'::[]))))) r'
        in
        (match filtered_var with
         | [] ->
           CoreErlang.Coq_term_call ((CoreErlang.Coq_term_globl r_modpath),
             (CoreErlang.Coq_term_globl r'),
             (map (fun x0 -> extr_ast0 e x0) xs))
         | m :: l ->
           (match l with
            | [] ->
              CoreErlang.Coq_term_call ((CoreErlang.Coq_term_globl
                r_modpath), (CoreErlang.Coq_term_globl r'),
                (map (fun x0 -> extr_ast0 e x0) xs))
            | f0 :: l0 ->
              (match l0 with
               | [] ->
                 CoreErlang.Coq_term_call ((CoreErlang.Coq_term_globl m),
                   (CoreErlang.Coq_term_globl f0),
                   (map (fun x0 -> extr_ast0 e x0) xs))
               | c :: l1 ->
                 CoreErlang.Coq_term_call ((CoreErlang.Coq_term_globl
                   r_modpath), (CoreErlang.Coq_term_globl r'),
                   (map (fun x0 -> extr_ast0 e x0) xs)))))
      | x0 ->
        let f' = extr_ast0 e x0 in
        (match f' with
         | CoreErlang.Coq_term_letrec (defs, t0) ->
           (match t0 with
            | CoreErlang.Coq_term_var v ->
              CoreErlang.Coq_term_letrec (defs, (CoreErlang.Coq_term_apply
                ((CoreErlang.Coq_term_var v),
                (map (fun x1 -> extr_ast0 e x1) xs))))
            | x1 ->
              CoreErlang.Coq_term_apply (f',
                (map (fun x2 -> extr_ast0 e x2) xs)))
         | x1 ->
           CoreErlang.Coq_term_apply (f',
             (map (fun x2 -> extr_ast0 e x2) xs))))
   | Miniml.MLlam (wildcard', wildcard'0) ->
     let (bl, t') = collect_lams t in
     let (bl', e') = push_vars (map id_of_mlid bl) e in
     CoreErlang.Coq_term_fun (CoreErlang.Coq_func
     ((map (fun s -> CoreErlang.Coq_var (string_of_id s)) (rev bl')),
     (extr_ast0 e' t')))
   | Miniml.MLletin (v, e1, e2) ->
     let (bl, e') = push_vars ((id_of_mlid v) :: []) e in
     (match bl with
      | [] -> assert false (* absurd case *)
      | v' :: l ->
        (match l with
         | [] ->
           let e1' = extr_ast0 e e1 in
           let e2' = extr_ast0 e' e2 in
           CoreErlang.Coq_term_let ((CoreErlang.Coq_var (string_of_id v')),
           e1', e2')
         | i :: l0 -> assert false (* absurd case *)))
   | Miniml.MLglob r ->
     let r' = pp_global Term r in
     if is_inline_custom r
     then CoreErlang.Coq_term_custom r'
     else CoreErlang.Coq_term_globl r'
   | Miniml.MLcons (wildcard', r, xs) ->
     CoreErlang.Coq_term_lit ((CoreErlang.Coq_lit_cons (pp_global Cons r)),
       (map (fun x0 -> extr_ast0 e x0) xs))
   | Miniml.MLtuple xs ->
     CoreErlang.Coq_term_lit (CoreErlang.Coq_lit_tup,
       (map (fun x0 -> extr_ast0 e x0) xs))
   | Miniml.MLcase (wildcard', t', br) ->
     let extr_branch = fun b ->
       let (ids, p, t'0) = b in
       let (ids', e') = push_vars (map id_of_mlid ids) e in
       CoreErlang.Coq_clause ((extr_pat e' p (rev ids')),
       (CoreErlang.Coq_term_lit ((CoreErlang.Coq_lit_atom
       ((function s ->
     let r = String.create (List.length s) in
     let rec fill pos = function
       | [] -> r
       | c :: s -> r.[pos] <- c; fill (pos + 1) s
     in fill 0 s)
         ('t'::('r'::('u'::('e'::[])))))), [])), (extr_ast0 e' t'0))
     in
     let t'' = extr_ast0 e t' in
     let clauses = Array.to_list (Array.map extr_branch br) in
     let as_case = CoreErlang.Coq_term_case (t'', clauses) in
     (match t'' with
      | CoreErlang.Coq_term_apply (t0, l) ->
        (match t0 with
         | CoreErlang.Coq_term_fname f ->
           let CoreErlang.Coq_fname (a, n) = f in
           ((fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ ->
              as_case)
              (fun n0 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ ->
                as_case)
                (fun n1 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ ->
                  match l with
                  | [] -> as_case
                  | delay :: l0 ->
                    (match l0 with
                     | [] -> as_case
                     | default :: l1 ->
                       (match l1 with
                        | [] ->
                          if CoreErlang.atom_eq_dec a
                               ('r'::('e'::('c'::('e'::('i'::('v'::('e'::('_'::('f'::('i'::('n'::[])))))))))))
                          then CoreErlang.Coq_term_recv (clauses, delay,
                                 default)
                          else as_case
                        | t1 :: l2 -> as_case)))
                  (fun n2 ->
                  as_case)
                  n1)
                n0)
              n)
         | x0 -> as_case)
      | x0 -> as_case)
   | Miniml.MLfix (k, ids, fns) ->
     let (ids', e') = push_vars (rev (Array.to_list ids)) e in
     let zip = fun n f ->
       let n' = string_of_id n in
       let (vs, f') = collect_lams f in
       let (vs', e'') = push_vars (map id_of_mlid vs) e' in
       let f'' = extr_ast0 e'' f' in
       CoreErlang.Coq_def ((CoreErlang.Coq_fname (n', (length vs'))),
       (CoreErlang.Coq_func
       ((rev (map (fun v -> CoreErlang.Coq_var (string_of_id v)) vs')),
       f'')))
     in
     let defs = map2 zip (rev ids') (Array.to_list fns) in
     let id =
       (function x -> function i -> x.(i)) (Array.of_list (rev ids'))
         (int_of_nat k)
     in
     CoreErlang.Coq_term_letrec (defs, (CoreErlang.Coq_term_var
     (CoreErlang.Coq_var_atom (string_of_id id))))
   | Miniml.MLexn s ->
     CoreErlang.Coq_term_primop
       (((function s ->
     let r = String.create (List.length s) in
     let rec fill pos = function
       | [] -> r
       | c :: s -> r.[pos] <- c; fill (pos + 1) s
     in fill 0 s)
          ('r'::('a'::('i'::('s'::('e'::[])))))), ((CoreErlang.Coq_term_lit
       ((CoreErlang.Coq_lit_atom
       ((function s ->
     let r = String.create (List.length s) in
     let rec fill pos = function
       | [] -> r
       | c :: s -> r.[pos] <- c; fill (pos + 1) s
     in fill 0 s)
         ('e'::('r'::('r'::('o'::('r'::[]))))))),
       [])) :: ((CoreErlang.Coq_term_lit ((CoreErlang.Coq_lit_str s),
       [])) :: [])))
   | Miniml.MLdummy ->
     CoreErlang.Coq_term_lit ((CoreErlang.Coq_lit_atom
       ((function s ->
     let r = String.create (List.length s) in
     let rec fill pos = function
       | [] -> r
       | c :: s -> r.[pos] <- c; fill (pos + 1) s
     in fill 0 s)
         ('d'::('u'::('m'::('m'::('y'::[]))))))), [])
   | Miniml.MLaxiom ->
     CoreErlang.Coq_term_primop
       (((function s ->
     let r = String.create (List.length s) in
     let rec fill pos = function
       | [] -> r
       | c :: s -> r.[pos] <- c; fill (pos + 1) s
     in fill 0 s)
          ('r'::('a'::('i'::('s'::('e'::[])))))), ((CoreErlang.Coq_term_lit
       ((CoreErlang.Coq_lit_atom
       ((function s ->
     let r = String.create (List.length s) in
     let rec fill pos = function
       | [] -> r
       | c :: s -> r.[pos] <- c; fill (pos + 1) s
     in fill 0 s)
         ('e'::('x'::('i'::('t'::[])))))), [])) :: ((CoreErlang.Coq_term_lit
       ((CoreErlang.Coq_lit_str
       ((function s ->
     let r = String.create (List.length s) in
     let rec fill pos = function
       | [] -> r
       | c :: s -> r.[pos] <- c; fill (pos + 1) s
     in fill 0 s)
         ('a'::('x'::('i'::('o'::('m'::(' '::('t'::('o'::(' '::('b'::('e'::(' '::('r'::('e'::('a'::('l'::('i'::('z'::('e'::('d'::[])))))))))))))))))))))),
       [])) :: [])))
   | Miniml.MLmagic t' -> extr_ast0 e t')

(** val extr_ast : Common.env -> Miniml.ml_ast -> CoreErlang.term_t **)

let extr_ast e t =
  extr_ast_func (ExistT (e, t))

(** val extr_decl : Miniml.ml_decl -> CoreErlang.def_t list **)

let extr_decl d =
  let extr_decl' = fun e r t ty ->
    if is_custom r
    then CoreErlang.Coq_def_custom ((pp_global Term r), (find_custom r))
    else let (bl, t') = collect_lams t in
         let (bl0, e') = push_vars (map id_of_mlid bl) e in
         CoreErlang.Coq_def ((CoreErlang.Coq_fname ((pp_global Term r),
         (length bl0))), (CoreErlang.Coq_func
         ((map (fun i -> CoreErlang.Coq_var (string_of_id i)) (rev bl0)),
         (extr_ast e' t'))))
  in
  (match d with
   | Miniml.Dind (mi, ind) -> []
   | Miniml.Dtype (r, id, tys) -> []
   | Miniml.Dterm (r, t, ty) -> (extr_decl'  (empty_env ())  r t ty) :: []
   | Miniml.Dfix (rs, asts, tys) ->
     map3 (extr_decl'  (empty_env ()) ) (Array.to_list rs)
       (Array.to_list asts) (Array.to_list tys))

(** val extr_defs :
    (Names.label * Miniml.ml_structure_elem) list -> CoreErlang.def_t list **)

let rec extr_defs x =
  let extr_defs0 = fun defs -> extr_defs defs in
  (match x with
   | [] -> []
   | d :: defs' ->
     let (wildcard', m0) = d in
     (match m0 with
      | Miniml.SEdecl dec -> app (extr_decl dec) (extr_defs0 defs')
      | Miniml.SEmodule m ->
        let filtered_var = (function e -> e.ml_mod_expr) m in
        (match filtered_var with
         | Miniml.MEstruct (path', m1) ->
           let defs'' = m1 in app (extr_defs0 defs'') (extr_defs0 defs')
         | x0 -> extr_defs0 defs')
      | Miniml.SEmodtype m -> extr_defs0 defs'))

(** val def_names : CoreErlang.def_t list -> CoreErlang.fname_t list **)

let rec def_names = function
| [] -> []
| d :: ds' ->
  (match d with
   | CoreErlang.Coq_def (n, f) ->
     let CoreErlang.Coq_fname (a, k) = n in
     if (=) k 0 then def_names ds' else n :: (def_names ds')
   | CoreErlang.Coq_def_custom (c, c0) -> def_names ds')

(** val extr_struct : Miniml.ml_structure -> CoreErlang.module_t list **)

let extr_struct mlss =
  let extr_struct' = fun mls ->
    let (path, struct0) = mls in
    let mk_defs = fun x -> let defs' = struct0 in extr_defs defs' in
    let defs =
      (function mp -> function sel -> function f -> push_visible mp sel; let p = f () in pop_visible (); p)
        path [] mk_defs
    in
    CoreErlang.Coq_module ((string_of_mp path), (def_names defs), [], defs)
  in
  map extr_struct' mlss

(** val str : char list -> Pp.std_ppcmds **)

let str s =
  Pp.str
    ((function s ->
     let r = String.create (List.length s) in
     let rec fill pos = function
       | [] -> r
       | c :: s -> r.[pos] <- c; fill (pos + 1) s
     in fill 0 s)
      s)

(** val pp_atom : CoreErlang.atom_t -> Pp.std_ppcmds **)

let pp_atom a =
  let r' =
    Str.regexp
      ((function s ->
     let r = String.create (List.length s) in
     let rec fill pos = function
       | [] -> r
       | c :: s -> r.[pos] <- c; fill (pos + 1) s
     in fill 0 s)
        ('\''::[]))
  in
  let q =
    (function s ->
     let r = String.create (List.length s) in
     let rec fill pos = function
       | [] -> r
       | c :: s -> r.[pos] <- c; fill (pos + 1) s
     in fill 0 s)
      ('@'::[])
  in
  (++) (str ('\''::[]))
    ((++) (Pp.str (Str.global_replace r' q a)) (str ('\''::[])))

(** val pp_fname : CoreErlang.fname_t -> Pp.std_ppcmds **)

let pp_fname = function
| CoreErlang.Coq_fname (a, n) ->
  (++) (pp_atom a) ((++) (str ('/'::[])) (Pp.int (int_of_nat n)))

(** val pp_concat : Pp.std_ppcmds list -> Pp.std_ppcmds **)

let rec pp_concat ps =
  fold_right (++) (str []) ps

(** val pp_concat_sep :
    Pp.std_ppcmds -> Pp.std_ppcmds list -> Pp.std_ppcmds **)

let rec pp_concat_sep s = function
| [] -> str []
| a :: ps' ->
  (match ps' with
   | [] -> a
   | s0 :: l -> (++) a ((++) s (pp_concat_sep s ps')))

(** val pp_var : CoreErlang.var_t -> Pp.std_ppcmds **)

let pp_var v =
  let rlc =
    Str.regexp
      ((function s ->
     let r = String.create (List.length s) in
     let rec fill pos = function
       | [] -> r
       | c :: s -> r.[pos] <- c; fill (pos + 1) s
     in fill 0 s)
        ('^'::('['::('a'::('-'::('z'::(']'::[])))))))
  in
  let r' =
    Str.regexp
      ((function s ->
     let r = String.create (List.length s) in
     let rec fill pos = function
       | [] -> r
       | c :: s -> r.[pos] <- c; fill (pos + 1) s
     in fill 0 s)
        ('\''::[]))
  in
  let a =
    (function s ->
     let r = String.create (List.length s) in
     let rec fill pos = function
       | [] -> r
       | c :: s -> r.[pos] <- c; fill (pos + 1) s
     in fill 0 s)
      ('@'::[])
  in
  (match v with
   | CoreErlang.Coq_var s ->
     let s' = Str.global_replace r' a s in
     if Str.string_match rlc s' (int_of_nat 0)
     then (++) (str ('_'::[])) (Pp.str s')
     else Pp.str s'
   | CoreErlang.Coq_var_atom s ->
     (++) (str ('\''::[]))
       ((++) (Pp.str (Str.global_replace r' a s)) (str ('\''::[]))))

(** val pp_lit :
    Pp.std_ppcmds -> CoreErlang.lit_t -> Pp.std_ppcmds list -> Pp.std_ppcmds **)

let pp_lit spc l args =
  match l with
  | CoreErlang.Coq_lit_int i -> Pp.int i
  | CoreErlang.Coq_lit_atom a -> pp_atom a
  | CoreErlang.Coq_lit_char c -> str ('\''::(c::('\''::[])))
  | CoreErlang.Coq_lit_str s ->
    (++) (str ('"'::[])) ((++) (Pp.str s) (str ('"'::[])))
  | CoreErlang.Coq_lit_nil -> str ('['::(']'::[]))
  | CoreErlang.Coq_lit_cons s ->
    let default =
      if CoreErlang.atom_eq_dec s []
      then (match args with
            | [] ->
              (++) (str ('{'::(' '::[])))
                ((++)
                  (pp_concat_sep
                    ((++) (Pp.fnl ()) ((++) spc (str (','::(' '::[])))))
                    args) ((++) (Pp.fnl ()) ((++) spc (str ('}'::[])))))
            | arg :: l0 ->
              (match l0 with
               | [] -> (++) (str ('{'::[])) ((++) arg (str ('}'::[])))
               | s0 :: l1 ->
                 (++) (str ('{'::(' '::[])))
                   ((++)
                     (pp_concat_sep
                       ((++) (Pp.fnl ()) ((++) spc (str (','::(' '::[])))))
                       args) ((++) (Pp.fnl ()) ((++) spc (str ('}'::[])))))))
      else (match args with
            | [] -> pp_atom s
            | arg :: l0 ->
              (match l0 with
               | [] ->
                 (++) (str ('{'::[]))
                   ((++) (pp_atom s)
                     ((++) (str (','::(' '::[]))) ((++) arg (str ('}'::[])))))
               | s0 :: l1 ->
                 (++) (str ('{'::(' '::[])))
                   ((++)
                     (pp_concat_sep
                       ((++) (Pp.fnl ()) ((++) spc (str (','::(' '::[])))))
                       ((pp_atom s) :: args))
                     ((++) (Pp.fnl ()) ((++) spc (str ('}'::[])))))))
    in
    if CoreErlang.atom_eq_dec s ('C'::('o'::('n'::('s'::[]))))
    then (match args with
          | [] -> default
          | a :: l0 ->
            (match l0 with
             | [] -> default
             | b :: l1 ->
               (match l1 with
                | [] ->
                  (++) (str ('['::[]))
                    ((++) a ((++) (str ('|'::[])) ((++) b (str (']'::[])))))
                | s0 :: l2 -> default)))
    else if CoreErlang.atom_eq_dec s ('N'::('i'::('l'::[])))
         then (match args with
               | [] -> str ('['::(']'::[]))
               | s0 :: l0 -> default)
         else default
  | CoreErlang.Coq_lit_tup ->
    (match args with
     | [] ->
       (++) (str ('{'::(' '::[])))
         ((++)
           (pp_concat_sep
             ((++) (Pp.fnl ()) ((++) spc (str (','::(' '::[]))))) args)
           ((++) (Pp.fnl ()) ((++) spc (str ('}'::[])))))
     | arg :: l0 ->
       (match l0 with
        | [] -> (++) (str ('{'::[])) ((++) arg (str ('}'::[])))
        | s :: l1 ->
          (++) (str ('{'::(' '::[])))
            ((++)
              (pp_concat_sep
                ((++) (Pp.fnl ()) ((++) spc (str (','::(' '::[]))))) args)
              ((++) (Pp.fnl ()) ((++) spc (str ('}'::[])))))))

(** val pp_pat : Pp.std_ppcmds -> CoreErlang.pat_t -> Pp.std_ppcmds **)

let rec pp_pat spc = function
| CoreErlang.Coq_pat_var v -> pp_var v
| CoreErlang.Coq_pat_lit (l, ps) -> pp_lit spc l (map (pp_pat spc) ps)
| CoreErlang.Coq_pat_alias (v, p') ->
  (++) (pp_var v)
    ((++) (str (' '::('='::(' '::[]))))
      (pp_pat ((++) spc (str (' '::(' '::(' '::[]))))) p'))

(** val pp_term : Pp.std_ppcmds -> CoreErlang.term_t -> Pp.std_ppcmds **)

let rec pp_term spc t =
  let pp_fun0 = fun f ->
    let CoreErlang.Coq_func (vars, t0) = f in
    let vars' = pp_concat_sep (str (','::(' '::[]))) (map pp_var vars) in
    let spc' = (++) spc (str (' '::(' '::[]))) in
    (++) (str ('f'::('u'::('n'::(' '::('('::[]))))))
      ((++) vars'
        ((++) (str (')'::(' '::('-'::('>'::(' '::[]))))))
          ((++) (Pp.fnl ()) ((++) spc' (pp_term spc' t0)))))
  in
  let pp_clause = fun spc0 c ->
    let spc' = (++) spc0 (str (' '::(' '::(' '::(' '::[]))))) in
    let CoreErlang.Coq_clause (pat, guard, body) = c in
    (++) (pp_pat spc0 pat)
      ((++) (str (' '::('w'::('h'::('e'::('n'::(' '::[])))))))
        ((++) (pp_term spc0 guard)
          ((++) (str (' '::('-'::('>'::[]))))
            ((++) (Pp.fnl ()) ((++) spc' (pp_term spc' body))))))
  in
  (match t with
   | CoreErlang.Coq_term_var v -> pp_var v
   | CoreErlang.Coq_term_fname f -> pp_fname f
   | CoreErlang.Coq_term_lit (l, ts) -> pp_lit spc l (map (pp_term spc) ts)
   | CoreErlang.Coq_term_fun fn -> pp_fun0 fn
   | CoreErlang.Coq_term_let (v, t1, t2) ->
     let spc' = (++) spc (str (' '::(' '::[]))) in
     (++) (str ('l'::('e'::('t'::(' '::[])))))
       ((++) (pp_var v)
         ((++) (str (' '::('='::(' '::[]))))
           ((++) (Pp.fnl ())
             ((++) spc'
               ((++) (pp_term spc' t1)
                 ((++) (Pp.fnl ())
                   ((++) spc
                     ((++) (str ('i'::('n'::(' '::[]))))
                       (pp_term ((++) spc (str (' '::(' '::(' '::[]))))) t2)))))))))
   | CoreErlang.Coq_term_case (t0, cs) ->
     let spc' = (++) spc (str (' '::(' '::[]))) in
     (++) (str ('c'::('a'::('s'::('e'::(' '::[]))))))
       ((++)
         (pp_term ((++) spc (str (' '::(' '::(' '::(' '::(' '::[]))))))) t0)
         ((++) (str (' '::('o'::('f'::[]))))
           ((++) (Pp.fnl ())
             ((++) spc'
               ((++)
                 (pp_concat_sep ((++) (Pp.fnl ()) spc')
                   (map (pp_clause spc') cs))
                 ((++) (Pp.fnl ())
                   ((++) spc (str (' '::('e'::('n'::('d'::[]))))))))))))
   | CoreErlang.Coq_term_letrec (defs, t0) ->
     let pp_def = fun d ->
       match d with
       | CoreErlang.Coq_def (fn, f) ->
         (++) (pp_fname fn) ((++) (str (' '::('='::(' '::[])))) (pp_fun0 f))
       | CoreErlang.Coq_def_custom (c, b) -> str []
     in
     (++) (str ('l'::('e'::('t'::('r'::('e'::('c'::(' '::[]))))))))
       ((++)
         (pp_concat_sep
           ((++) (Pp.fnl ())
             ((++) spc
               (str
                 (' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::[])))))))))))
           (map pp_def defs))
         ((++) (Pp.fnl ())
           ((++) spc
             ((++) (str ('i'::('n'::(' '::[]))))
               (pp_term ((++) spc (str (' '::(' '::(' '::[]))))) t0)))))
   | CoreErlang.Coq_term_apply (t0, args) ->
     (match args with
      | [] ->
        let spc' =
          (++) (Pp.fnl ())
            ((++) spc
              (str
                (' '::(' '::(' '::(' '::(' '::(' '::(','::(' '::[]))))))))))
        in
        let args' =
          pp_concat_sep spc'
            (map
              (pp_term
                ((++) spc
                  (str
                    (' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::[])))))))))))
              args)
        in
        (++) (str ('a'::('p'::('p'::('l'::('y'::(' '::[])))))))
          ((++) (pp_term ((++) spc (str (' '::(' '::[])))) t0)
            ((++) (Pp.fnl ())
              ((++) spc
                ((++)
                  (str
                    (' '::(' '::(' '::(' '::(' '::(' '::('('::(' '::[])))))))))
                  ((++) args'
                    ((++) (Pp.fnl ())
                      ((++) spc
                        (str
                          (' '::(' '::(' '::(' '::(' '::(' '::(')'::[])))))))))))))))
      | arg :: l ->
        (match l with
         | [] ->
           (++) (str ('a'::('p'::('p'::('l'::('y'::(' '::[])))))))
             ((++) (pp_term ((++) spc (str (' '::(' '::[])))) t0)
               ((++) (str (' '::('('::[])))
                 ((++) (pp_term ((++) spc (str (' '::(' '::[])))) arg)
                   (str (')'::[])))))
         | t1 :: l0 ->
           let spc' =
             (++) (Pp.fnl ())
               ((++) spc
                 (str
                   (' '::(' '::(' '::(' '::(' '::(' '::(','::(' '::[]))))))))))
           in
           let args' =
             pp_concat_sep spc'
               (map
                 (pp_term
                   ((++) spc
                     (str
                       (' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::[])))))))))))
                 args)
           in
           (++) (str ('a'::('p'::('p'::('l'::('y'::(' '::[])))))))
             ((++) (pp_term ((++) spc (str (' '::(' '::[])))) t0)
               ((++) (Pp.fnl ())
                 ((++) spc
                   ((++)
                     (str
                       (' '::(' '::(' '::(' '::(' '::(' '::('('::(' '::[])))))))))
                     ((++) args'
                       ((++) (Pp.fnl ())
                         ((++) spc
                           (str
                             (' '::(' '::(' '::(' '::(' '::(' '::(')'::[])))))))))))))))))
   | CoreErlang.Coq_term_call (m, f, args) ->
     (match args with
      | [] ->
        let spc' =
          (++) (Pp.fnl ())
            ((++) spc
              (str (' '::(' '::(' '::(' '::(' '::(','::(' '::[])))))))))
        in
        let args' =
          pp_concat_sep spc'
            (map
              (pp_term
                ((++) spc
                  (str (' '::(' '::(' '::(' '::(' '::(' '::(' '::[]))))))))))
              args)
        in
        (++) (str ('c'::('a'::('l'::('l'::(' '::[]))))))
          ((++) (pp_term ((++) spc (str (' '::(' '::[])))) m)
            ((++) (str (':'::[]))
              ((++) (pp_term ((++) spc (str (' '::(' '::[])))) f)
                ((++) (Pp.fnl ())
                  ((++) spc
                    ((++)
                      (str
                        (' '::(' '::(' '::(' '::(' '::('('::(' '::[]))))))))
                      ((++) args'
                        ((++) (Pp.fnl ())
                          ((++) spc
                            (str
                              (' '::(' '::(' '::(' '::(' '::(')'::[]))))))))))))))))
      | arg :: l ->
        (match l with
         | [] ->
           (++) (str ('c'::('a'::('l'::('l'::(' '::[]))))))
             ((++) (pp_term ((++) spc (str (' '::(' '::[])))) m)
               ((++) (str (':'::[]))
                 ((++) (pp_term ((++) spc (str (' '::(' '::[])))) f)
                   ((++) (str (' '::('('::[])))
                     ((++) (pp_term ((++) spc (str (' '::(' '::[])))) arg)
                       (str (')'::[])))))))
         | t0 :: l0 ->
           let spc' =
             (++) (Pp.fnl ())
               ((++) spc
                 (str (' '::(' '::(' '::(' '::(' '::(','::(' '::[])))))))))
           in
           let args' =
             pp_concat_sep spc'
               (map
                 (pp_term
                   ((++) spc
                     (str
                       (' '::(' '::(' '::(' '::(' '::(' '::(' '::[]))))))))))
                 args)
           in
           (++) (str ('c'::('a'::('l'::('l'::(' '::[]))))))
             ((++) (pp_term ((++) spc (str (' '::(' '::[])))) m)
               ((++) (str (':'::[]))
                 ((++) (pp_term ((++) spc (str (' '::(' '::[])))) f)
                   ((++) (Pp.fnl ())
                     ((++) spc
                       ((++)
                         (str
                           (' '::(' '::(' '::(' '::(' '::('('::(' '::[]))))))))
                         ((++) args'
                           ((++) (Pp.fnl ())
                             ((++) spc
                               (str
                                 (' '::(' '::(' '::(' '::(' '::(')'::[]))))))))))))))))))
   | CoreErlang.Coq_term_primop (a, args) ->
     (++) (str ('p'::('r'::('i'::('m'::('o'::('p'::(' '::[]))))))))
       ((++) (pp_atom a)
         ((++) (str (' '::('('::[])))
           ((++)
             (pp_concat_sep (str (','::(' '::[])))
               (map (pp_term (str [])) args)) (str (')'::[])))))
   | CoreErlang.Coq_term_try (e1, vs, e2, cs, e3) ->
     let spc' = (++) spc (str (' '::(' '::[]))) in
     let spc'' = (++) spc' (str (' '::(' '::[]))) in
     (++) (str ('t'::('r'::('y'::(' '::[])))))
       ((++) (pp_term ((++) spc (str (' '::(' '::(' '::(' '::[])))))) e1)
         ((++) (str (' '::('o'::('f'::[]))))
           ((++) (Pp.fnl ())
             ((++) spc'
               ((++) (pp_concat_sep (str (','::(' '::[]))) (map pp_var vs))
                 ((++) (str (' '::('-'::('>'::(' '::[])))))
                   ((++) (Pp.fnl ())
                     ((++) spc''
                       ((++) (pp_term spc'' e2)
                         ((++) (Pp.fnl ())
                           ((++) spc
                             ((++)
                               (str
                                 ('c'::('a'::('t'::('c'::('h'::(' '::[])))))))
                               ((++)
                                 (pp_concat_sep (str (','::(' '::[])))
                                   (map pp_var vs))
                                 ((++) (str (' '::('-'::('>'::(' '::[])))))
                                   ((++) (Pp.fnl ())
                                     ((++) spc'' (pp_term spc'' e3)))))))))))))))))
   | CoreErlang.Coq_term_recv (cs, t1, t2) ->
     let spc' = (++) spc (str (' '::(' '::[]))) in
     (++) (str ('r'::('e'::('c'::('e'::('i'::('v'::('e'::(' '::[])))))))))
       ((++) (pp_concat_sep (str (' '::[])) (map (pp_clause spc') cs))
         ((++) (str (' '::('a'::('f'::('t'::('e'::('r'::[])))))))
           ((++) (Pp.fnl ())
             ((++) spc'
               ((++) (pp_term spc' t1)
                 ((++) (str (' '::('-'::('>'::[]))))
                   ((++) (Pp.fnl ()) ((++) spc' (pp_term spc' t2)))))))))
   | CoreErlang.Coq_term_do (t1, t2) ->
     let spc' = (++) spc (str (' '::(' '::(' '::[])))) in
     (++) (str ('d'::('o'::(' '::[]))))
       ((++) (pp_term spc' t1)
         ((++) (Pp.fnl ()) ((++) spc' (pp_term spc' t2))))
   | CoreErlang.Coq_term_catch t0 ->
     (++) (str ('c'::('a'::('t'::('c'::('h'::(' '::[])))))))
       (pp_term ((++) spc (str (' '::(' '::[])))) t0)
   | CoreErlang.Coq_term_globl s -> pp_atom s
   | CoreErlang.Coq_term_custom s -> Pp.str s)

(** val pp_fun : CoreErlang.fun_t -> Pp.std_ppcmds **)

let pp_fun = function
| CoreErlang.Coq_func (vars, t) ->
  let vars' = pp_concat_sep (str (','::(' '::[]))) (map pp_var vars) in
  let spc' = str (' '::(' '::[])) in
  (++) (str ('f'::('u'::('n'::(' '::('('::[]))))))
    ((++) vars'
      ((++) (str (')'::(' '::('-'::('>'::(' '::[]))))))
        ((++) (Pp.fnl ()) ((++) spc' (pp_term spc' t)))))

(** val pp_decl0 : CoreErlang.def_t -> Pp.std_ppcmds **)

let pp_decl0 = function
| CoreErlang.Coq_def (fn, f) ->
  let CoreErlang.Coq_fname (a, k) = fn in
  if (=) k 0
  then str []
  else (++) (pp_fname fn) ((++) (str (' '::('='::(' '::[])))) (pp_fun f))
| CoreErlang.Coq_def_custom (c, b) ->
  (++) (str ('%'::(' '::[])))
    ((++) (Pp.str c) ((++) (str (' '::('='::('>'::(' '::[]))))) (Pp.str b)))

(** val pp_struct0 : CoreErlang.module_t list -> Pp.std_ppcmds **)

let pp_struct0 mods =
  let pp_struct' = fun m ->
    let CoreErlang.Coq_module (nam, exports, attrs, defs) = m in
    let nam' = pp_atom nam in
    let exports' =
      pp_concat_sep (str (','::(' '::[]))) (map pp_fname exports)
    in
    (++) (str ('m'::('o'::('d'::('u'::('l'::('e'::(' '::[]))))))))
      ((++) nam'
        ((++) (str (' '::('['::(' '::[]))))
          ((++) exports'
            ((++)
              (str
                (' '::(']'::(' '::('a'::('t'::('t'::('r'::('i'::('b'::('u'::('t'::('e'::('s'::(' '::('['::(' '::(']'::(' '::[])))))))))))))))))))
              ((++) (Pp.fnl ())
                ((++) (pp_concat_sep (Pp.fnl ()) (map pp_decl0 defs))
                  ((++) (Pp.fnl ())
                    ((++) (str ('e'::('n'::('d'::[]))))
                      ((++) (Pp.fnl ()) (Pp.fnl ()))))))))))
  in
  pp_concat (map pp_struct' mods)

(** val preamble0 :
    Names.identifier -> Names.module_path list -> Miniml.unsafe_needs ->
    Pp.std_ppcmds **)

let preamble0 nam imports h =
  str []

(** val sig_preamble0 :
    Names.identifier -> Names.module_path list -> Miniml.unsafe_needs ->
    Pp.std_ppcmds **)

let sig_preamble0 h list0 h0 =
  str []

(** val pp_sig0 : Miniml.ml_signature -> Pp.std_ppcmds **)

let pp_sig0 h =
  str []

(** val coreerlang_descr : Miniml.language_descr **)

let coreerlang_descr =
  { Miniml.keywords = keywords0; Miniml.file_suffix = file_suffix0;
    Miniml.preamble = preamble0; Miniml.pp_struct = (fun x ->
    pp_struct0 (extr_struct x)); Miniml.sig_suffix = sig_suffix0;
    Miniml.sig_preamble = sig_preamble0; Miniml.pp_sig = pp_sig0;
    Miniml.pp_decl = (fun x -> pp_concat (map pp_decl0 (extr_decl x))) }


