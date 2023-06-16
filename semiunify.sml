(* COPYRIGHT (c) Martin Emms and Hans Leiss, Univ.Muenchen,   22.8.97 

   Version 1.5. Adapted to SML/NJ Version 110.0.3,   March 98, H.Leiss
   Version 1.6. Adapted to SML/NJ Version 110.99.3, June 2023, H.Leiss
                (list of changes: at the end of this file)
*)

signature SEMIUNIFY =
  sig
    type disp
    val show: disp ref
    datatype ineqlabel = mylab of (Access.access * Symbol.symbol) 
    datatype ineq = ineq of (ineqlabel*int*Types.ty*Types.ty)
    type monoconstraint 
    val monoConstraintsAsIneqns : monoconstraint list -> ineq list
    val compress : (Types.ty list) ref -> unit
    val solve : ineq list -> (monoconstraint list) -> ineq list
    exception SFAIL of string * ineq * (ineq list)
end


structure Semiunify : SEMIUNIFY   = 
 struct

local open 
    Array List Types VarCon Access BasicTypes TypesUtil Unify Absyn
    ErrorMsg PrettyPrint PPUtil PPType PPAbsyn

in 

val viewsemi = ElabControl.viewsemi
val showsemi = ElabControl.showsemi

val nullRegion = SourceMap.nullRegion

val makestring = Int.toString

exception NotThere

datatype ineq = ineq of (ineqlabel*int*ty*ty)
and ineqlabel = mylab of (Access.access * Symbol.symbol) 

type monoconstraint = (ineqlabel * (ty list) ref) 
and  disp = ineq list * ineq list -> string -> ineq list * ineq list

val vars    = ref([]:ty list)
and thecase = ref("Reduction case")
and show    = ref(fn (y:ineq list * ineq list) => fn (x:string) =>  y)

fun revadd (a::acc) list = revadd acc (a::list)
  | revadd [] list = list

fun memberTy x (y::rest) = 
    if equalType(x,y) then true else (memberTy x rest)
  | memberTy x [] = false
and addTy (el,[]) = [el]
  | addTy (el,elem::set) = if equalType(el,elem) then (elem::set) 
                              else (elem::(addTy(el,set)))

fun eqIneq(ineq(lab,i,ty1,ty2),ineq(lab',i',ty1',ty2')) =
    lab=lab' andalso i=i' andalso 
    equalType(ty1,ty1') andalso equalType(ty2,ty2')
and addIneq (el,[]) = [el]
  | addIneq (el,elem::set) = if eqIneq(el,elem) then (elem::set) 
                             else (elem::(addIneq(el,set)))
                     
fun openvariable s = case prune(s) of 
    VARty(ref(OPEN{depth,...})) => true     
  | VARty(ref(OVLDV{eq,sources})) => true       (* used in red3 *)
  | VARty(ref(OVLDI _ | OVLDW _)) => true       (* used in red3 *)
  | _ => false

fun freevars t = 
    case prune(t) of
	VARty(ref(OPEN{kind = FLEX fields,...})) => ((* vars := (t::(!vars)); *)
						app freevars (map #2 fields))
      | VARty(_) => if (openvariable t) 
			then (if (memberTy t (!vars)) then () 
			      else (vars := (t::(!vars))))
		    else ()
      | CONty(f,args) => app freevars args 
      | _ => ()

fun lowerDepth n t = case (prune t) 
    of VARty(tv as ref(OPEN{depth=d,eq,kind})) 
        => tv := OPEN{depth=Int.min(d,n),eq=eq,kind=kind}
      | VARty(tv as ref(UBOUND{depth=d,eq,name}))
        => tv := UBOUND{depth=Int.min(d,n),eq=eq,name=name}
(*    | VARty(tv as ref(LBOUND{depth=d,num})) 
        => tv := LBOUND{depth=Int.min(d,n),num=num}  (* needed?? *) 
*)
      | VARty(tv as ref(LBOUND{depth=d,eq=b,index=num})) 
        => tv := LBOUND{depth=Int.min(d,n),eq=b,index=num} 
      | VARty _ => ()
      | CONty(tc,tys) => app (lowerDepth n) tys
      | POLYty{sign,tyfun=TYFUN{arity,body}} 
        => lowerDepth n body
      | _ => ()
and maxDepth t = case (prune t)
    of VARty(tv as ref(OPEN{depth=d,eq,kind})) => d
     | VARty(tv as ref(UBOUND{depth=d,eq,name})) => d
     | VARty(tv as ref(LBOUND{depth=d,...})) => d
     | VARty _ => 0
     | CONty(tc,tys) => foldr Int.max 0 (map maxDepth tys)
     | POLYty{sign,tyfun=TYFUN{arity,body}} => maxDepth body
     | _ => 0

(* Semiunify tests whether var x in x <lab t is monomorphic for lab. *)

(* The type variables in type assumptions of lambda-bound individual
   variables in the context of a declaration have to be treated as
   monomorphic types when typing occurrences of the declared variables
   in the declaration body. 
   As this list of type variable is the same for all simultaneously
   declared variables (ineqlabels), they all ref(er) to this list.
*)
     
fun isMono (ty,lab) ((l,m)::monos) =    (* Assumes: all tys in monos are tyvars *)
    if lab = l then memberTy (prune ty) (!m) else isMono (ty,lab) monos
  | isMono (ty,lab) [] = false
and monoConstraintsAsIneqns ((label,m)::monos) = 
    (map (fn x => ineq(label,0,x,x)) (!m)) @ (monoConstraintsAsIneqns monos)
  | monoConstraintsAsIneqns [] = []
and flattenMonoconstraints ((lab,m)::monos) = 
    (compress m; flattenMonoconstraints monos)
  | flattenMonoconstraints ([] : monoconstraint list) = ()
and compress (r as ref(tylist)) =  
    let fun g [] = [] 
          | g (x::y) = (let val x' = (vars := []; freevars x; (!vars)) 
                            val _ = vars := [] 
                        in  
                            (x' @ g(y)) 
                        end) 
        fun collect [] cs = cs 
          | collect (b::bs) cs = collect bs (addTy (b,cs))
    in  
        r := collect (map prune (g tylist)) [] 
    end 


(* THE REWRITES ON A SEMIUNIFY PROBLEM *)

exception SFAIL of string * ineq * (ineq list)

(* reduce1:  reduces one instance of f1(args1) < f1(args2) *)

exception Red1 of ineq list
exception DecomposeClash of ineq
exception DecomposeUndef

fun red1 (e::rest, acc) = 
    (((decompose e) @ rest, acc)
     handle DecomposeUndef => red1 (rest, e::acc)
          | DecomposeClash(eqn) => 
         raise SFAIL("function clash in semiunification",eqn,
                     (revadd acc (e::rest))))
  | red1 ([], acc) = raise Red1(acc)

and decompose (ineq(lab,i,x,y)) =
    (case (headReduceType (prune x),headReduceType (prune y)) 

         of (CONty(tycon1,args1),CONty(tycon2,args2)) =>
             if eqTycon(tycon1,tycon2) then 
                 let fun mkIneqns [] [] = []
                       | mkIneqns (x1::rest1) (x2::rest2) = 
                         addIneq (ineq(lab,i,x1,x2),(mkIneqns rest1 rest2))
                 in 
                     (thecase := "by Reduce1 with <"^(makestring i)^" (decompose types):"; 
                      rev (mkIneqns args1 args2))
                 end 
             else raise DecomposeClash(ineq(lab,i,x,y))

          | (VARty(v as ref(OPEN{kind = FLEX fields,
                                 eq=e,
                                 depth=d})), CONty(tycon,_)) =>
             (case tycon 
                  of (RECORDtyc labellist) =>
                      (let fun member x [] = false 
                             | member x ((x',ty)::rest) = 
	                           if (x = x') then true else (member x rest)
                           fun extras [] l = []
			     | extras (x::rest) l = 
                               if (member x l) then (extras rest l)
                               else ((x,VARty(ref(OPEN{kind=META,
                                                       eq=e,
                                                       depth=d})))
                                     :: (extras rest l))
                           val labels = map #1 (fields @ extras labellist fields)
                           val types  = map #2 (fields @ extras labellist fields)
                       in (v := INSTANTIATED (CONty(RECORDtyc labels,types));
                           thecase := "by Reduce1 with <"^(makestring i)^
                           " (flexible record case):";
                           [ineq(lab,i,x,y)])
                       end)
                | _ => raise DecomposeClash(ineq(lab,i,x,y)))

          | (_,_) => raise DecomposeUndef)



(* reduce1a: discard x <{f,i} t, with side-effect x=t, for overloaded
             tyvar x or if x is constraint to give f-matchers(x) = x *)

exception Red1a of ineq list

fun red1a ((e as ineq(lab,i,x,y))::rest,acc) monol = 
    (case (headReduceType (prune x)) of
      (* VARty(ref(SCHEME(eq))) => (* 0.93: VARty(ref(OPEN{depth=0,...})) olvd *) *)
         VARty(ref(OVLDV{eq,sources})) =>
             (unifyTy(x,y,nullRegion,nullRegion) handle Unify(mode) =>
                 raise SFAIL("function clash in semiunification",
                             e, revadd acc (e::rest))
              ; thecase := 
                     "By Reduce1a with <"^(makestring i)^ " (schematic var case):";
                     (revadd acc rest,[]))
         | VARty(ref(OVLDI _ | OVLDW _)) =>  
             (unifyTy(x,y,nullRegion,nullRegion) handle Unify(mode) =>
                 raise SFAIL("function clash in semiunification",
                             e, revadd acc (e::rest))
              ; thecase := 
                     "By Reduce1a with <"^(makestring i)^ " (literal var case):";
                     prune y; (* avoid compiler bug: unexpected tyvar INSTANTIATED in translate *)
                     (revadd acc rest,[]))
       | tv => if isMono(x,lab) monol then
                  (unifyTy(x,y,nullRegion,nullRegion) handle Unify(mode) =>
                      raise SFAIL("function clash in semiunification",
                                  e, revadd acc (e::rest))
                   ; thecase := 
                      "By Reduce1a with <"^(makestring i)^ " (monomorphic var case):";
                      (revadd acc rest,[]))
               else (case tv 
                         of VARty(ref(OPEN{depth=d,...})) 
                             => if maxDepth y > d then
                                    (thecase := "By Reduce1a with <"^(makestring i)^ 
                                     " (lower rhs tyvar depths)"; 
                                     lowerDepth d y; 
                                     (revadd acc (e::rest),[]))
                                else red1a (rest,e::acc) monol
                           | _ => red1a (rest,e::acc) monol))
  | red1a ([],acc) monol = raise Red1a(acc)



(* reduce2: reduces a pair  x <i t, x <i s  to  x <i t, with side-effect t=s *)

(* Inequation `x <_{lab,n} t' corresponds to the n-th occurrence of an 
   individual variable; the name of this variable, `lab', is added to increase
   readability of semi-unification output.

   The `monoconstraints' related to all occurrences of individual variable `lab' 
   are established when passing the polymorphic binder(!) of `lab'; their effect
   is as if inequations 

            x <_{lab,n} x     for all occurrences n>0 

   were added to the semiunification inequations. They enforce that x is treated
   as a monomorphic variable.
*)

exception Red2 of ineq list
exception FIND

fun red2 ((e as ineq(lab,i,x,t))::rest, acc) =
    if openvariable(x) then 
        (let 
             val (ineq(lab,j,y,s)::restr, accr) = find (lab,i,x) (rest, [])
         in 
             (thecase := "By Reduce2 with <"^(makestring i)^
              " (unify rhd sides, for same tyvar on lhs)";
              unifyTy(t,s,nullRegion,nullRegion) handle Unify(mode) => 
                  raise SFAIL ("instantiability failure in semiunification:\n\
                               \  (instances of same tyvar in <"^(makestring i)^" don't unify)",
                               ineq(lab,i,tupleTy[x,y],tupleTy[t,s]),
                               revadd acc (e::rest));
             (revadd acc rest, []))          (* search for red1-2 redexes anew *)
         end                   
	      handle FIND => red2 (rest, ineq(lab,i,x,t)::acc))
    else red2 (rest, e::acc)
  | red2 ([], acc) = raise Red2(acc)

and find (lab,i,x) ((e as ineq(label,j,y,_)) :: ineqs, acc) =
    if i=j then 
       if equalType(y,x) then (e::ineqs,acc)
       else find (lab,i,x) (ineqs, e::acc)
    else raise FIND (* ineqns s <_{i,lab} t form a connected subsequence of ineqns! *)
  | find (lab,i,x) _ = raise FIND


(* reduce3:   eliminates f(args) < x, substitutes copy(f(args)) for x *)

(* generalized occurs check function *)

fun check x y S =    (* x ineq ... ineq y in S *)
  equalType(x,y) 
  orelse (let val S' = minus(y,S) (* so y not made a dtr again *)
	  in iterate (fn dtr => (check x dtr S')) (daughters(y,S)) 
	  end)

and daughters (y,ineqns) =
    let fun dtrs (y,ineq(_,_,x,y')::rest,acc) =  
	     if equalType(y,y') then dtrs (y,rest,x::acc) else dtrs (y,rest,acc)
          |  dtrs (y,[],acc) = acc
    in dtrs (y,ineqns,[])
    end

and minus (y,ineqns) =
    let fun minusAux (y,(ineq(lab,i,y',z)::rest),acc) = 
	     if equalType(y,y') then minusAux (y,rest,acc)
	     else minusAux (y,rest,ineq(lab,i,y',z)::acc)
          | minusAux (y,[],acc) = rev acc
    in minusAux (y,ineqns,[])
    end

and iterate f (x::rest) = if f(x) then true else (iterate f rest)
  | iterate f [] = false  


exception Red3 of ineq list

fun copyTy t =                          (* different from typecheck.copyTy *)
   let val newineqs = ref([]:(ty*ty) list)
       fun lookup ty =
	    let fun find [] = raise NotThere
		  | find((ty1,ty2)::rest) = if equalType(ty,ty1) then ty2 
							else find rest
	     in find(!newineqs)
	    end

       fun copy1 t = case (prune t)
	   of CONty(f,args) => CONty(f,(map copy1 args))
	 |  v as VARty(ref(UBOUND{...})) => v
	 |  VARty(tv as ref(OPEN{kind=FLEX(fields),depth=d,eq=eq})) => 
		let 
		    fun f (lab,ty) = (lab,copy1 ty) 
		in (tv := OPEN{kind=FLEX(map f fields),depth=d,eq=eq};
		    VARty(tv))
		end
	 |  v as VARty(ref(OPEN{depth=d,eq=eq,kind=k})) =>
		(lookup v handle NotThere =>
		    let val v1 = VARty(ref(OPEN{depth=d,eq=eq,kind=k}))
		    in (newineqs := ((v,v1)::(!newineqs));v1)
		    end)
	 | _ => t
   in (copy1 t,!newineqs)
   end

fun red3 ((e as ineq(lab,i,t,v))::rest, acc) =
    (case (prune t) of 
         CONty(f,args) => 
             (if openvariable v then 
                  if (* does occurs-check *) 
                      (iterate (fn var => (check v var (revadd acc (e::rest))))
                       (vars:= ([]:ty list);freevars(t);(!vars))) then
                      raise SFAIL("extended occurs check failure in semiunification",
                                  e, revadd acc (e::rest))
                  else let 
                           val (t',pairs) = copyTy(t)
                       in 
                           (thecase := "by Reduce3 with <"^(makestring i)^
                            " (unify rhs var with \ncopy of lhs non-var, and decompose):";
                            unifyTy(t',v,nullRegion,nullRegion) handle Unify(mode) =>
                                raise SFAIL("function clash in semiunification",
                                            e, revadd acc (e::rest))
                            ; 
                            (revadd acc (revadd (map (fn (x,y) => ineq(lab,i,x,y)) pairs)
                                        rest), []))
                       end
              else red3 (rest, e::acc))
       | _ => red3 (rest, e::acc))
  | red3 ([], acc) = raise Red3(acc)


(* Main function; keep order of inequations only when viewing/stepping *)

fun solve ineql monol = 
    let fun process (Left,Right) monol = 
            if (!viewsemi) > (!(# Step showsemi))
                then
                    process (!show (red1(Left,Right)) (!thecase)) monol
                    handle Red1(reduced1) =>
                        (flattenMonoconstraints monol;
                         process(!show (red1a(rev reduced1,[]) monol) (!thecase)) monol
                         handle Red1a(reduced1a) =>
                             process(!show (red2(rev reduced1a,[])) (!thecase)) monol
                             handle Red2(reduced2) =>
                                 process(!show (red3(rev reduced2,[])) (!thecase)) monol
                                 handle Red3(reduced3) => rev reduced3)
                                      
            else 
                process (red1(Left,Right)) monol
                handle Red1(reduced1) =>
                    (flattenMonoconstraints monol;
                     process (red1a(reduced1,[]) monol) monol
                     handle Red1a(reduced1a) =>
                         process (red2(reduced1a,[])) monol
                         handle Red2(reduced2) =>
                             process (red3(reduced2,[])) monol                   
                             handle Red3(reduced3) => reduced3)
    in 
        process (ineql,[]) monol
    end
end (* local *)
end (* Semiunify structure *)


(* H.L.:

28.9.97: Separated monoConstraints from the other ineqns to avoid 
         handling unnecessary constraints in Var/Rule case of the
         typechecker. (Now simpler as in the correctness proof.)

8.2.98:  Share monoConstraints for simultaneously declared variables.
         Added monoconstraint and monocConstraintsAsIneqns to the
         signature SEMIUNIFY

12.2.98  Fixed a bug in red3, to restart reducing the whole system. 

13.3.98  Adapted to SML/NJ Version 110. 

 - sig SEMIUNIFY: removed openvariable, vars, freevars; added compress
 - used equalType instead of = in memberTy and (prune x = prune y)
 - replaced equiv(x,y) = (prune x = prune y) by equalType(x,y) in check
 - replaced ty=ty1 by equalType(ty,ty1) in lookup in copyTy
 - replaced addOnce by addTy and addIneq 
 - renamed Process to solve
 - added LITERAL and SCHEME as open(ty)vars to handle  ty < tyvar.
 
 - unclear: what about LBOUND tyvars? These seem to occur only later 
   when translating to lambda-tys.

24.3.98:
 - added lowerDepth case in red1a to remove bug in typing embedded 
   simultaneous recursions to avoid incorrect type quantification.

15.6.23:
 - added
     val viewsemi = ElabControl.viewsemi
     val showsemi = ElabControl.showsemi
 - replaced                          by
     Control_CG.viewsemi               viewsemi
     Control_CG.showsemi               showsemi
     VARty(ref(SCHEME(eq))             VARty(ref(OVLDV{eq,sources}))
     VARty(ref(LITERAL{kind,region})   VARty(ref(OVLDI _ | OVLDW _))
     VARty(ref(LBOUND{depth,num}))     VARty(ref(LBOUND{depth,eq,index}))
     unifyTy(x,y)                      unifyTy(x,y,nullRegion,nullRegion)
 - removed
     open Overload TyvarSet
*)
