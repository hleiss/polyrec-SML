(* Examples showing some differences between monomorphic and 
   polymorphic recursion.

   The main practical advantage of polymorphic recursion is that

   - within mutually recursive definitions, less type clashes occur
   - on datatypes with increasing type parameters, functions by 
     structural recursion are possible.

   A promising application of polymorphic recursion is dimension in-
   ferece as suggested by M.Rittri (see reference below). M.Tofte used 
   an approximation to polymorphic recursion to do region inference 
   in his KIT compiler for SML.
*)

(* I. Difference in domain types: *)

structure Example1 =
 struct
     fun f x = f 1
 end

(* 
ML+: structure Example1 : sig val f : 'a -> 'b end
ML:  structure Example1 : sig val f : int -> 'a end

However,
ML+: fun f x = f (x+1) : int -> 'a  via monotype of x
*)


structure Example2 =
 struct
     fun  f x = (f 1; f "a"; x)
 end

(* 
ML+: structure Example2 : sig val f : 'a -> 'a end
ML Error: operator and operand don't agree [literal]
  operator domain: int
  operand:         string
  in expression:
    f "a"
*)

(* 2. Difference in range type: *)

structure Example3 =
    struct
        fun f x = (0+(f x); f x)
    end

(*
ML+: structure Example3 : sig val f : 'a -> 'b end
ML:  structure Example3 : sig val f : 'a -> int end
*)

structure Example4 =
    struct
        fun f x = (0+(f x); "a"^(f x); f x)
    end

(*
ML+: structure Example4 : sig val f : 'a -> 'b end
ML: Error: operator and operand don't agree [literal]
  operator domain: string * string
  operand:         string * int
  in expression:
    "a" ^ f x
*)


(* 3. Simultaneous definitions with expected principal type in ML+,
      but less general principal type or untypable in ML. 

      However, the functions are ML-typable if defined separately.
*)

structure Example5 = (* A.Mycroft[1984] *)
 struct
     fun I x = x 
     and J x = I x 
     and K x = J (x + 1)  
 end

(* 
ML+: structure Example5 :
  sig
    val I : 'a -> 'a
    val J : 'a -> 'a
    val K : int -> int
  end

  This is the result with ML+ based on smlnj-110.0.3. For smlnj-110.99.03,
  we obtain the same only if we turn of the "sanitiy check" 

      (** just a sanity check; should turn it off later **)
      val (b1,b2) =
        if LT.ff_eqv (fflag, fflag') then LT.ffd_fspec fflag
        else bug "unexpected code in lpfd"

  in base/compiler/FLINT/opt/specialize.sml, i.e. replace this by
  
      val (b1,b2) = LT.ffd_fspec fflag'

  (where fflag' corresponds to the type of the defining fn-expression,
   fflag to the type of the functions usage in the fn body).

ML: structure Example5 :
  sig
    val I : int -> int
    val J : int -> int
    val K : int -> int
  end
*)

structure Example6 =
 struct
     fun map f [] = []  
       | map f (x::l) = (f x) :: (map f l)
     and neglist l = map not l
     and sqrlist l = map (fn x:int => x * x) l
 end

(* 
ML+: structure Example6 :
  sig
    val map : ('a -> 'b) -> 'a list -> 'b list
    val neglist : bool list -> bool list
    val sqrlist : int list -> int list
  end

ML Error: operator and operand don't agree [tycon mismatch]
  operator domain: bool -> bool
  operand:         int -> int
  in expression:
    map (fn x : int => x * x)
*)


(* 4. Simultaneous definitions with expected principal type in ML+,
      but untypable in ML. 
      The definitions cannot be separated and then typed in ML.
*)

structure Example7 = 
 struct
     fun test x = if (x + 1) = 3 then true else false 
     and f x = if x = [] then [] 
               else (length(g(tl x))::(f(g(tl x)))) 
     and g x = if x = [] then [] 
               else (test(hd(f x))::(g(tl(f x)))) 
 end

(* 
ML+: structure Example7 :
  sig
    val f : ''a list -> int list
    val g : ''a list -> bool list
    val test : int -> bool
  end
ML: Error: operator and operand don't agree [tycon mismatch]
  operator domain: bool * bool list
  operand:         bool * int list
  in expression:
    test (hd (f x)) :: g (tl (f x))
*)


structure Example8 = (* A.Mycroft[1984] Monomorphic rec restricts code sharing *)
 struct
     datatype lista = aEmpty | acons of int * lista
     datatype listb = bEmpty | bcons of string * listb 
     datatype 'a cases = basecase of 'a | acase of lista | bcase of listb

     fun ahd (acons(x,_)) = basecase(x)
     fun atl (acons(_,y)) = y
     fun anull aEmpty = true 

     fun bhd (bcons(x,_)) = basecase(x)
     fun btl (bcons(_,y)) = y
     fun bnull bEmpty = true 
         
     fun f x = case x of 
         (basecase(y)) => ()
       | (acase(y)) => g(y,(ahd,atl,anull))
       | (bcase(y)) => g(y,(bhd,btl,bnull)) 

     and g (x,(xhd,xtl,xnull)) =
         (if (xnull x) then () else (f(xhd(x)) ;  g(xtl x,(xhd,xtl,xnull))))
 end

(*
ML+: structure Example8 :
  sig
    datatype 'a cases = acase of lista | basecase of 'a | bcase of listb
    datatype lista = aEmpty | acons of int * lista
    datatype listb = bEmpty | bcons of string * listb
    val ahd : lista -> int cases
    val anull : lista -> bool
    val atl : lista -> lista
    val bhd : listb -> string cases
    val bnull : listb -> bool
    val btl : listb -> listb
    val f : 'a cases -> unit
    val g : 'a * (('a -> 'b cases) * ('a -> 'a) * ('a -> bool)) -> unit
  end

ML: Error: operator and operand don't agree [tycon mismatch]
  operator domain: lista
                   * ((lista -> int cases) * (lista -> lista)
                      * (lista -> bool))
  operand:         listb
                   * ((listb -> string cases) * (listb -> listb)
                      * (listb -> bool))
  in expression:
    g (y,(bhd,btl,bnull))
*)

structure Example9 = (* Th.Altenkirch, ML-list July 1995. 
   weak_tm calls weak_subst at non-unifiable types, but these are instances 
   of the definition type of weak_subst, which also calls weak_tm.
*)     
 struct
     datatype Tm = t_var of int | 
         t_c of string*Tm |
         t_case of Tm*(Pat Subst) |
         t_lam of Tm Bind | t_app of Tm*Tm |
         t_tup of Tm list | t_let of Tm Subst 
     withtype 'a Bind = int*int*(string list)*'a
     and      'a Subst = ('a Bind)*Tm
     and      Pat  = (string*(Tm Bind)) list

     fun weak_bind wk (mn as (m,n)) ((m',n',xs,t) :'a Bind) = 
         if m<m' 
             then (m'+n,n',xs,wk mn t) : 'a Bind
         else (m',n',xs,wk (m+n',n) t)

     exception Internal_error of string

     fun weak_tm (m,n) (t_var j) = 
         if m<=j then t_var (j+n) else t_var j
       | weak_tm mn (t_c (c,t)) =
             t_c (c,weak_tm mn t)
       | weak_tm mn (t_case (t,p)) =
             t_case (weak_tm mn t,weak_subst weak_pat mn p)
       | weak_tm mn (t_lam b) =
             t_lam(weak_bind weak_tm mn b)
       | weak_tm mn (t_app (t,t')) =
             t_app (weak_tm mn t,weak_tm mn t')
       | weak_tm mn (t_tup ts) =
             t_tup (map (weak_tm mn) ts)
       | weak_tm mn (t_let s) =
             t_let (weak_subst weak_tm mn s)
     and weak_subst wk mn (b,t) = 
         (weak_bind wk mn b,weak_tm mn t)
     and weak_pat mn cbs = map (fn (c,b) => (c,weak_bind weak_tm mn b)) cbs
     and weak_con (mn as (m,n)) (n',xs,ts) =
         let fun weak_con' 0 [] = []
               | weak_con' i (t::ts) =
             (weak_tm (m+i-1,n) t)::(weak_con' (i-1) ts)
               | weak_con' _ _ = 
             raise Internal_error "weak_con: sick context"
         in (n',xs,weak_con' n' ts)
         end
 end

(*
ML+: structure Example9 :
  sig
    type 'a Bind = int * int * string list * 'a
    type Pat = (string * Tm Bind) list
    type 'a Subst = 'a Bind * Tm
    datatype Tm
      = t_app of Tm * Tm
      | t_c of string * Tm
      | t_case of Tm * Pat Subst
      | t_lam of Tm Bind
      | t_let of Tm Subst
      | t_tup of Tm list
      | t_var of int
    exception Internal_error of string
    val weak_bind : (int * int -> 'a -> 'a) -> int * int -> 'a Bind -> 'a Bind
    val weak_con : int * int -> int * 'a * Tm list -> int * 'a * Tm list
    val weak_pat : int * int -> ('a * Tm Bind) list -> ('a * Tm Bind) list
    val weak_subst : (int * int -> 'a -> 'a)
                     -> int * int -> 'a Bind * Tm -> 'a Bind * Tm
    val weak_tm : int * int -> Tm -> Tm
  end

ML: Error: operator and operand don't agree [tycon mismatch]
  operator domain: Pat Subst
  operand:         Tm Subst
  in expression:   ((weak_subst weak_tm) mn) s
Error: right-hand-side of clause doesn't agree with function result type [tycon mismatch]
  expression:  int * int -> Tm Bind * Tm -> Tm Bind * Tm
  result type:  int * int -> Pat Subst -> Pat Subst
  in declaration:  weak_subst = (fn arg => (fn <pat> => <exp>))
Error: right-hand-side of clause doesn't agree with function result type [tycon mismatch]
  expression:  ('Z * Tm Bind) list -> ('Z * Tm Bind) list
  result type:  Tm -> Tm
  in declaration:  weak_pat = (fn arg => (fn <pat> => <exp>))
*)



(* 5. Recursive functions on data types with increasing type parameter.
   Such datatypes are definable in SML, but monomorphic recursion forbids to
   do structural recursion on objects of these datatypes. (!!)
*)

structure Example10 = (* R.Milner,C.P.Wadsworth 197? *)
 struct
     datatype 'a Tree = Empty | Node of ('a * (('a Tree) Tree))
     fun flatten [] = [] 
       | flatten (x::y) = x @ (flatten y)
     fun collect Empty = [] 
       | collect (Node(x,y)) = x :: (flatten (map collect (collect y)))
 end

(*
ML+: structure Example10 :
  sig
    datatype 'a Tree = Empty | Node of 'a * 'a Tree Tree
    val collect : 'a Tree -> 'a list
    val flatten : 'a list list -> 'a list
  end
ML: Error: operator and operand don't agree [circularity]
  operator domain: 'Z Tree
  operand:         'Z Tree Tree
  in expression:
    collect y
*)


structure Example11 = (* M.Rittri[1995] *)
    struct
        datatype ('a,'b) Trapez = Naught 
          | & of ('a * 'b) * (('a, ('a * 'b)) Trapez);
        infixr &;

        type triangle = (int,unit) Trapez;

        fun fstCol Naught = []
          | fstCol ((x,_) & rows) = x :: (fstCol rows)

        val tria = (1,()) & 
                   (2, (3,())) &
                   (4, (5, (6, ()))) & Naught
    end

(* 
ML+: structure Example11 :
  sig
    datatype ('a,'b) Trapez = & of ('a * 'b) * ('a,'a * 'b) Trapez | Naught
    type triangle = (int,unit) Trapez
    val fstCol : ('a,'b) Trapez -> 'a list
    val tria : (int,unit) Trapez
  end

ML:Error: operator and operand don't agree [circularity]
  operator domain: ('Z,'Y) Trapez
  operand:         ('Z,'Z * 'Y) Trapez
  in expression:
    fstCol rows
*)


structure Example12 = (* Example 13 simplified; trie with 2-dim. key *)
 struct      
    type const = int
        
    datatype key = 
        Const of const | Pair of key * key
    datatype 'a ctree = 
        EmptyC | C of const * 'a * ('a ctree)
    datatype 'a ptree =
        EmptyP | P of ('a ctree) * (('a ptree) ptree)
        
    fun find (P(C(i,a,t),_), Const(j)) = 
        if j=i then a else find (P(t, EmptyP), Const(j))
      | find (P(_,t), Pair(p,q)) = find (find (t,p), q)
end

(* 
ML+: Warning: match nonexhaustive
          (P (C (<pat>,<pat>,<pat>),_),Const j) => ...
          (P (_,t),Pair (p,q)) => ...
  
structure Example12 :
  sig
    type const = int
    datatype 'a ctree = C of const * 'a * 'a ctree | EmptyC
    datatype key = Const of const | Pair of key * key
    datatype 'a ptree = EmptyP | P of 'a ctree * 'a ptree ptree
    val find : 'a ptree * key -> 'a
  end

Error: operator and operand don't agree [circularity]
  operator domain: 'Z ptree * key
  operand:         'Z ptree ptree * key
  in expression:
    find (t,p)
*)


structure Example13 = (* C.Elliott, types list 1991 *)
 struct
     type const = int

     type 'a const_dtree = (const * 'a) list;

     fun cd_find ([], _, fc, sc) = fc ()
       | cd_find ((acon,a) :: rest, con, fc, sc) 
         = (if acon = con then (sc (a, fc))
            else  cd_find (rest, con, fc, sc))
     and cd_merge (ctree, cTree) = ctree @ cTree;

     datatype exp = 
         Var of string
       | Const of const
       | Appl of exp * exp
     and 'a exp_dtree =
         Empty_ed
       | Ed of 'a option * 'a const_dtree * ('a exp_dtree) exp_dtree;

     type 'b fcont = unit -> 'b
     type ('a,'b) scont = 'a * 'b fcont -> 'b;

     fun anyfc (SOME anyval, fc, sc) =
         (fn () => sc (anyval, fc))
       | anyfc (NONE, fc, _) = fc;

     fun ed_find (Empty_ed, _, fc, _) = fc ()
       | ed_find (Ed (opt_anyval, _, _), Var(str), fc, sc) =
         anyfc (opt_anyval, fc, sc) ()
       | ed_find (Ed (opt_anyval, ctree, _), Const(con), fc, sc) = 
         cd_find (ctree, con, anyfc (opt_anyval, fc, sc), sc)
       | ed_find (Ed (opt_anyval, _, atree), Appl(f, arg), fc, sc) = 
         ed_find (atree, f, anyfc (opt_anyval, fc, sc), 
                  (fn (arg_tree, fun_fc) => ed_find (arg_tree, arg, fun_fc, sc)));

     fun opt_merge (NONE, SOME anyval) = SOME anyval
       | opt_merge (SOME anyval, NONE) = SOME anyval
       | opt_merge (SOME anyval, SOME anyVal) = SOME anyval
       | opt_merge (_, _) = NONE;

     fun ed_merge (Empty_ed, t) = t
       | ed_merge (s, Empty_ed) = s
       | ed_merge (Ed (optval, ctree, etree), Ed (optVal, cTree, eTree)) =
         Ed (opt_merge (optval, optVal), 
             cd_merge (ctree, cTree),
             ed_merge (etree, eTree));

     fun ed_insert Empty_ed (Var(str), a) = 
         Ed (SOME a, [], Empty_ed)
       | ed_insert Empty_ed (Const(con), a) = 
         Ed (NONE, [(con,a)], Empty_ed)
       | ed_insert Empty_ed (Appl(e1,e2), a) = 
         Ed (NONE, [], (ed_insert Empty_ed (e1, ed_insert Empty_ed (e2,a))))
       | ed_insert (Ed (_,ctree,etree)) (Var(str), a) = 
         Ed (SOME a, ctree, etree)
       | ed_insert (Ed (opt,ctree,etree)) (Const(con), a) = 
         Ed (opt, (con,a) :: ctree, etree)
       | ed_insert (Ed (opt,ctree,etree)) (Appl(e1,e2), a) = 
         Ed (opt, ctree, ed_insert etree (e1, ed_insert Empty_ed (e2,a)))
 end

(* 
ML+: structure Example13 :
  sig
    type const = int
    type 'a const_dtree = (const * 'a) list
    datatype exp = Appl of exp * exp | Const of const | Var of string
    datatype 'a exp_dtree
      = Ed of 'a option * 'a const_dtree * 'a exp_dtree exp_dtree | Empty_ed
    type 'a fcont = unit -> 'a
    type ('a,'b) scont = 'a * 'b fcont -> 'b
    val anyfc : 'a option * (unit -> 'b) * ('a * (unit -> 'b) -> 'b)
                -> unit -> 'b
    val cd_find : (''a * 'b) list * ''a * (unit -> 'c)
                  * ('b * (unit -> 'c) -> 'c)
                  -> 'c
    val cd_merge : 'a list * 'a list -> 'a list
    val ed_find : 'a exp_dtree * exp * (unit -> 'b) * ('a * (unit -> 'b) -> 'b)
                  -> 'b
    val ed_insert : 'a exp_dtree -> exp * 'a -> 'a exp_dtree
    val ed_merge : 'a exp_dtree * 'a exp_dtree -> 'a exp_dtree
    val opt_merge : 'a option * 'a option -> 'a option
  end
 
ML: Error: operator and operand don't agree [circularity]
  operator domain: 'Z exp_dtree * exp * (unit -> 'Y)
                   * ('Z * (unit -> 'Y) -> 'Y)
  operand:         'Z exp_dtree exp_dtree * exp * (unit -> 'Y)
                   * ('Z exp_dtree * (unit -> 'Y) -> 'Y)
  in expression:
    ed_find
      (atree,f,anyfc (opt_anyval,fc,sc),(fn (<pat>,<pat>) => ed_find <exp>))

  (plus 4 more [circularity] error messages)   
*)


structure Example14 = (* Jim Hook, Stefan Kahrs (communicated by Thorsten Altenkirch)
   Implementation of untyped lambda terms (in #Lift free vars, using 
   deBruijn-indices).

   The triple ('a Lam, var, bindLam) forms a Kleisli-triple 
   (a' T, unitT : 'a -> 'a T, bindT : ('a -> 'b T) -> 'a T -> 'b T), i.e.

   1. f:'a -> 'b T  =  (bindT f) o unitT
   2. id : 'a T -> 'a T  =  (bindT unitT) 
   3. (bind T (f:'b -> 'c T  o  g:'a -> 'b))
      =  (bindT f) o (bindT (unitT o g)) : 'a T -> 'c T
*)
    struct
        datatype 'a Lam = var of 'a | app of ('a Lam) * ('a Lam) 
          | abs of ('a Lift) Lam
        and 'a Lift = new | old of 'a

        fun bindLam f (var x) = f x
          | bindLam f (app (t,u)) = app (bindLam f t,bindLam f u)
          | bindLam f (abs t) = abs (bindLam (liftLam f) t)

        and liftLam f new = var new
          | liftLam f (old x) = bindLam (var o old) (f x)

        and subst t u = bindLam (fn new => u | old x => var x) t

        and size (var _) = 1
          | size (app (t,u)) = (size t) + (size u)
          | size (abs t) = (size t) + 1

        val t = abs (app (var new, var (old new)))  (* lambda x.xy *)
    end

(* Since the definition of 'a Lam uses ('a Lift) Lam, recursive functions
   on 'a Lam (bindLam, LiftLam, subst, size) are untyple in ML. ML+ infers:

ML+: structure Example14 :
  sig
    datatype 'a Lam = abs of 'a Lift Lam | app of 'a Lam * 'a Lam | var of 'a
    datatype 'a Lift = new | old of 'a
    val bindLam : ('a -> 'b Lam) -> 'a Lam -> 'b Lam
    val liftLam : ('a -> 'b Lam) -> 'a Lift -> 'b Lift Lam
    val size : 'a Lam -> int
    val subst : 'a Lift Lam -> 'a Lam -> 'a Lam
    val t : 'a Lift Lam
  end

ML: Error: types of rules don't agree [circularity]
  earlier rule(s): ('Z Lift -> 'Y Lift Lam) * 'Z Lift Lam -> 'Y Lift Lam
  this rule: ('Z Lift -> 'Y Lift Lam) * 'Z Lam -> 'Y Lam
  in rule:
    (f,abs t) => abs ((bindLam (liftLam <exp>)) t)

  Error: case object and rules don't agree [circularity]
  rule domain: ('Z Lift -> 'Z Lift Lam) * 'Z Lift Lift
  object: ('Z Lift -> 'Z Lift Lift Lam) * 'Y
  in expression:
    (case (arg,arg)
      of (f,new) => var new
       | (f,old x) => (bindLam (<exp> o <exp>)) (f x))

  Error: operator and operand don't agree [circularity]
  operator domain: 'Z Lam
  operand:         'Z Lift Lam
  in expression:
    size t
*)


(* 7. Resolution of flexible records: 
      ML fixes the types of the fields, whereas ML+ does not.
*)

structure Example15 =
 struct
     fun f x = (# a x; f{a=2, b=true});
 end

(*
ML+: structure Example15 : sig val f : {a:'a, b:'b} -> 'c end
ML:  structure Example15 : sig val f : {a:int, b:bool} -> 'a end
*)

structure Example16 = 
 struct
     fun f x = (# 1 x; f(1,2); f("a",false); x)
 end

(* 
ML+: structure Example16 : sig val f : 'a * 'b -> 'a * 'b end
ML:  Error: operator and operand don't agree [literal]
  operator domain: int * int
  operand:         string * bool
  in expression:
    f ("a",false)
*)


(* 8. Flexible records are NOT resolved by context:

structure Example17 =
 struct
     val r = let fun f x = (# a x) in f{a=2,b=true} end;
 end

ML+, ML: Error: unresolved flex record
   (can't tell what fields there are besides #a)
   Warning: type vars not generalized because of
   value restriction are instantiated to dummy types (X1,X2,...)
*)


(* 9. Resolution of overloading in ML and ML+ is the same: *)

structure Example18 = 
 struct
     fun f x = (x; f 3.2)
     and g x = (x+x; g 3.2)
 end

(* 
ML+: structure Example18 :
  sig
    val f : 'a -> 'b
    val g : real -> 'a
  end
ML: structure Example18 :
  sig
    val f : real -> 'a
    val g : real -> 'a
  end
*)


(* 10. The generalization of types of embedded recursive definitions 
   is restricted by enclosing recursive definitions: *)

structure Example19 =
 struct
     fun f x = let fun g y = (x = f y; x) in g 0 end
 end

(* 
ML+: val f = fn : int -> int 

Inspecting the constraint solving (via Control.Elab.viewsemi := 2):

+ fun f x = let fun g y = (x = f y; x) in g 0 end;
Show recursive value case for:
val rec g = (fn y => (<exp>; <exp>)) ? y

Inequations before solving:          % Assumption f:'Z, x:'X, y:'Y
('Z  <1 f  'Y -> ''X)                % f:'Y -> ''X  at  f y
the monomorphic vars (instantiated):
(''X  <0 g  ''X)                     % ''X is monomorphic in def. of g

Step through solving the inequations? n
Inequations after solving: 
('Z  <1 f  'Y -> ''X)
the monomorphic vars (instantiated): % Context f:'Z, x:''X
(''X  <0 g  ''X)                     % results in g : 'Y -> ''X, 
                                     % NOT g : 'a -> ''X (!)
Show recursive value case for:
val rec f = (fn x => let <dec> in <exp> end) ? y

Inequations before solving: 
('Y  <2 g  int)                      % 'Y is instantiated to int at g 0
(''X -> ''X  <1 f  'Y -> ''X)        % fn x => let .. end : ''X -> ''X
the monomorphic vars (instantiated):
(''X  <0 g  ''X)
(''X  <0 g  ''X)

Step through solving the inequations? y
by Reduce1 with <1 (decompose types): print? y
('Y  <2 g  int)
(''X  <1 f  'Y)                      % ''X for typing f constraints 'Y
(''X  <1 f  ''X)                     % for typing g, though Y not in context!
the monomorphic vars (instantiated):
(''X  <0 g  ''X)
(''X  <0 g  ''X)

By Reduce2 with <1 (unify rhd sides, for same tyvar on lhs) print? y
(''Y  <2 g  int)
(''Y  <1 f  ''Y)
the monomorphic vars (instantiated):   % Now ''Y is monomorphic for g
(''Y  <0 g  ''Y)
(''Y  <0 g  ''Y)

By Reduce1a with <2 (monomorphic var case): print? y
(int  <1 f  int)
the monomorphic vars (instantiated):   % as ''Y is monomorphi for g, ''Y = int
(int  <0 g  int)                       % results in g : int -> int 
(int  <0 g  int)

By Reduce1a with <1 (literal var case): print? y
the monomorphic vars (instantiated):
(int  <0 g  int)
(int  <0 g  int)

Inequations after solving: 
the monomorphic vars (instantiated):
(int  <0 g  int)
(int  <0 g  int)

val f = fn : int -> int
+ 
*)


(* ---------------- Some ML+ untypable functions: -------------

structure Example20 =
 struct
     fun f x = (f x = "a"; 1);
 end

ML+: Error: unable to unify types in inequation system
  ('Z -> int  <1 f  'Z -> string)
  
  in declaration:
    val rec f = (fn x => (<exp>; <exp>))

(Derived type of f does not instantiate to 1st occurrence type of f in the body)

ML: Error: right-hand-side of clause does not agree with function result type 
[overload - bad instantiation]
  expression:  'Z[INT]
  result type:  string
  in declaration:
    f = (fn x => (f x = "a", 1))    [* bug in smlnj-110.99: ";" is turned into "," *]


structure Example21 =
 struct
     fun f x = f
 end

ML+: Error: extended occurs check failure in semiunification
  problem inequation
  ('Z -> 'Y  <1 f  'Y)
  
  in current system
  ('Z -> 'Y  <1 f  'Y)
  
  in declaration:
    val rec f = (fn x => f)

ML: Error: right-hand-side of clause does not agree with function result type [circularity]
  expression:  'Z -> 'Y
  result type:  'Y
  in declaration:
    f = (fn x => f)


The following examples are Damas-Milner typable, but *not* typable in SML/NJ Poly Rec!
For an explanation, see: polyrec/arity-problem.doc

structure Example22 = (* Recursive self-application  fix f.(f f) *)
 struct
     fun f x = f f x    
 end

ML+ (SML/NJ Version 0.93 [Poly Rec]): f : 'a -> 'b 
    (SML/NJ Version 110 [Poly Rec]) with smlnj-110.0.3
for the type:
TV(1,1)
Error: Compiler bug: LambdaType: unexpected case in tcd_arw

uncaught exception LtyArrow
  raised at: basics/ltyenv.sml:481.48-481.56

ML+ with SML/NJ Version 110.99.03:
Error: Compiler bug: LtyDef: unexpected tyc in tcd_parrow

These error messages come from the intermediate FLINT format. Setting

  Control.Elab.etopdebugging := true (* debug toplevel elaboration *)
  Control.Elab.viewsemi := 3         (* view checking val rec declarations *)
  Control.FLINT.plchk := true        (* Typecheck plambda expressions *)

and shows that elaboration (including type checking) succeeds and gives
an error message from type checking the intermediate PLambda expression:

+ fun f x = f f x;
>>elabTop
--elabTop.elab[dec]: calling ElabMod.elabDecl
Show recursive value case for:
val rec f = (fn x => (f f) x) ? y

Inequations before solving:       (* instantiate type 'Z -> 'Y of fn-expression     *)
('Z -> 'Y  <2 f  'X)              (* to type of 2nd occurrence of f in body (f f x) *)
('Z -> 'Y  <1 f  'X -> 'Z -> 'Y)  (* and to type of 1st occurrence of f in body     *) 

Step through solving the inequations? n
Inequations after solving: 
('Y  <1 f  'Z -> 'Y)
('Z  <1 f  'W -> 'V)
('Z  <2 f  'W)
('Y  <2 f  'V)

<<elabTop                         (* elaboration with polymorphic recursion succeeds *)
ERROR(checkLty): ltEquiv fails in ltMatch: APP:ltFnApp
le:
APP(v28, v28)

t1:
TYC(TV(1,0))
t2:
TYC(AR[cc]([TV(1,0)], [TV(1,1)]))
***************************************************

unexpected exception (bug?) in SML/NJ: Fail [Fail: ltMatch]
  raised at: ../compiler/FLINT/plambda/chkplexp.sml:177.35-177.49
             ../compiler/FLINT/plambda/chkplexp.sml:186.22
             ../compiler/Basics/stats/stats.sml:198.40
             ../compiler/TopLevel/interact/evalloop.sml:45.54

So, it seems, that the types (a' -> 'b) and 'a of the two 
occurrences of f in (f f) are checked for equivalence by ltEquiv,
corresponding to monomorphic recursion of ML:

ML: Error: operator and operand don't agree [circularity]
  operator domain: 'Z
  operand:         'Z -> 'Y
  in expression:
    f f


structure Example22 =
  struct
    fun f x = f (x,x)
  end

ML+ with SML/NJ Version 110.99.03:
Error: Compiler bug: OptUtils: unmatched list length in filter

while in loopify phase
  raised at:	../compiler/Basics/errormsg/errormsg.sml:55.14-55.19
		../compiler/Basics/stats/stats.sml:198.40
  end

Setting control flags as in Example21, we see how the semiunification
problem of the val rec declaration is solved (the unknown arg type 'Z
of f = (fn x ...) can be *instantiated to* the arg type 'Z * 'Z of f's use
in the body), but type checking the intermediate PLambda expression
tries to *unify* these types, and fails:

+ fun f x = f (x,x);
>>elabTop
--elabTop.elab[dec]: calling ElabMod.elabDecl
Show recursive value case for:
val rec f = (fn x => f (x,x)) ? y

Inequations before solving: 
('Z -> 'Y  <1 f  'Z * 'Z -> 'Y)

Step through solving the inequations? n
Inequations after solving: 
('Z  <1 f  'Z * 'Z)
('Y  <1 f  'Y)

<<elabTop
ERROR(checkLty): ltEquiv fails in ltMatch: APP:ltFnApp
le:
APP(v28, RCD(v29,v29))

t1:
TYC(TV(1,0))
t2:
TYC({TV(1,0),TV(1,0)})
***************************************************

unexpected exception (bug?) in SML/NJ: Fail [Fail: ltMatch]
  raised at: ../compiler/FLINT/plambda/chkplexp.sml:177.35-177.49
             ../compiler/FLINT/plambda/chkplexp.sml:186.22
             ../compiler/Basics/stats/stats.sml:198.40
             ../compiler/TopLevel/interact/evalloop.sml:45.54

Hence, the explanation in polyrec/arity-problem.doc is insufficient.

ML: Error: operator and operand do not agree [circularity]
  operator domain: 'Z
  operand:         'Z * 'Z
  in expression:
    f (x,x)


------------------------References: ---------------------------------

M.Rittri: Dimension Inference under Polymorphic Recursion. Proc. 7th
	ACM Conf. on Functional Programming and Computer Architecture, 1995

A.Mycroft: Polymorphic Type Schemes and Recursive Definitions. 
	Springer LNCS 167, pp.217-228, 1984 

*)


