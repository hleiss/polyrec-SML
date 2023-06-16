(* Source file : typing/typecheck.sml, Copyright 1989 by AT&T Bell Laboratories 
 *
 * Modified for typechecking with polymorphic recursion (Milner-Mycroft-types):
 * by M.Emms, June 1995/March 1997 and H.Leiss,April 1997/Oct 1997/March 1998
 *
 * (Copyright (c) M.Emms,H.Leiss 1997, {emms,leiss}@cis.uni-muenchen.de)         
 *
 * Version 1.6: Adaption to smlnj-110.99.3 by H.Leiss, June 2023, h.leiss@gmx.de
 *   - added
 *        val viewsemi = TypecheckControl.viewsemi
 *        val showsemi = TypecheckControl.showsemi
 *        missing case in patType (in typecheck.sml of 110.99.3)
 *              _ => bug "patType -- missing case in LAYEREDpat"
 *        local structure Semiunify
 *   - replaced
 *        Control.CG.viewsemi  by viewsemi
 *        Control.CG.showsemi  by showsemi
 *   - incorporated the changes of typecheck.sml of 110.99.3 over 110.0.3
 *        replace overload handling via OverLoadLit, LITERAL, SCHEME
 *                                   by Overload.new, OVLDI, OVLDW  
 *        replace unifyTy(ty1,ty2) by unifyTy(ty1,ty2,loc1,loc2)
 *                decType(...)     by decType(..,toplev,..,region) etc.
 *)

signature TYPECHECK = 
    sig
    
        val decType : StaticEnv.staticEnv * Absyn.dec * int * bool
            * ErrorMsg.errorFn * (unit -> bool) * SourceMap.region -> Absyn.dec
        (* decType(senv,dec,tdepth,toplev,err,region):
              senv: the context static environment
              dec: the declaration to be type checked
              tdepth: abstraction depth of lambda-bound type variables
              toplev: declaration at toplevel?
              err: error function
              region: source region of dec
         *)
        val debugging : bool ref
        
    end (* signature TYPECHECK *)

structure Typecheck : TYPECHECK =
    struct
    
        local open Types VarCon BasicTypes TypesUtil Unify Absyn
                   ErrorMsg PPUtil PPType PPAbsyn

              structure SE = StaticEnv
              structure DI = DebIndex
              structure DA = Access
              structure EU = ElabUtil
              structure ED = ElabDebug
              structure PP = PrettyPrint
              structure SU = Semiunify
              structure PPTL = PPTypelist
        in 

            (* typecheck control / debugging semiunification *)
            val viewsemi = TypecheckControl.viewsemi 
            val showsemi = TypecheckControl.showsemi

            (* debugging *)
            val say = Control_Print.say
            val debugging = ElabControl.tcdebugging (* ref false *)
            fun debugmsg (msg: string) = if !debugging then (say msg; say "\n") else ()
            val debugPrint = (fn x => ED.debugPrint debugging x)

            fun bug msg = ErrorMsg.impossible("TypeCheck: "^msg)

            infix 9 sub
            infix -->

            val printDepth = Control_Print.printDepth
            val showCulprits = ElabControl.showTypeErrorCulprits

            fun refNewDcon(DATACON{name,const,rep,typ,sign,lazyp}) = 
                DATACON{name=name,const=const,rep=rep,typ=refPatType,sign=sign,lazyp=lazyp}

            exception NotThere

            fun message(msg,mode: Unify.unifyFail) =
                String.concat[msg," [",Unify.failMessage mode,"]"]

            fun mkDummy0 () = BasicTypes.unitTy

(*
 * decType : SE.staticEnv * A.dec * DI.depth * bool * EM.errorFn * (unit -> bool) * region -> A.dec 
 *)
            fun decType(env,dec,tdepth,toplev,err,anyErrors,region) = 
                let

                (* setup for recording and resolving overloaded variables and literals *)
                    val { pushv = olv_push, pushl = oll_push, resolve = ol_resolve } = Overload.new ()

                    val ppType = PPType.ppType env
                    val ppTycon = PPType.ppTycon env
                    val ppPat = PPAbsyn.ppPat env
                    val ppExp = PPAbsyn.ppExp(env,NONE)
                    val ppRule = PPAbsyn.ppRule(env,NONE)
                    val ppVB = PPAbsyn.ppVB(env,NONE)
                    val ppRVB = PPAbsyn.ppRVB(env,NONE)
                    val ppDec = PPAbsyn.ppDec(env,NONE)
                    val ppDec' = (fn ppstrm => fn d => PPAbsyn.ppDec (env,NONE) ppstrm (d,!printDepth))

                    fun ppDecDebug (msg,dec) =
                        ED.withInternals(fn () => ED.debugPrint debugging (msg, ppDec', dec))

                    fun ppTypeDebug (msg,ty) =
                        ED.withInternals(fn () => ED.debugPrint debugging (msg, ppType, ty))

                    fun ppTyvarDebug tv = 
                        ED.withInternals(fn () => debugmsg (PPType.tyvarPrintname tv))

fun ppRegion ppstrm ((l,u): SourceMap.region) =
    (PP.string ppstrm (Int.toString l);
     PP.string ppstrm "-";
     PP.string ppstrm (Int.toString u))

fun ppModeErrorMsg ppstrm (mode: Unify.unifyFail) =
    if !showCulprits then
      (case mode
	of TYC(tyc1,tyc2,reg1,reg2) =>
	   (PP.newline ppstrm;
	    PP.string ppstrm "Mode: tycon mismatch"; PP.newline ppstrm;
	    PP.string ppstrm "tycon1: ";
	    ppTycon ppstrm tyc1; PP.newline ppstrm;
	    PP.string ppstrm "from: "; ppRegion ppstrm reg1; PP.newline ppstrm;
	    PP.string ppstrm "tycon2: ";
	    ppTycon ppstrm tyc2; PP.newline ppstrm;
	    PP.string ppstrm "from: "; ppRegion ppstrm reg2)
	 | TYP(ty1,ty2,reg1,reg2) =>
	   (PP.newline ppstrm;
	    PP.string ppstrm "Mode: type mismatch"; PP.newline ppstrm;
	    PP.string ppstrm "type1: ";
	    ppType ppstrm ty1; PP.newline ppstrm;
	    PP.string ppstrm "from: "; ppRegion ppstrm reg1; PP.newline ppstrm;
	    PP.string ppstrm "type2: ";
	    ppType ppstrm ty2; PP.newline ppstrm;
	    PP.string ppstrm "from: "; ppRegion ppstrm reg2)
	  | _ => ())
    else ()

(* setup for recording FLEX tyvars and checking that they are eventually
 * resolved to exact record types. This is to prevent the leakage of
 * unresolved flex record types into the middle end. *)
val flexTyVars : (tyvar * region) list ref = ref nil

fun registerFlex (x as (tv : tyvar, region: region)) =
    flexTyVars := x :: !flexTyVars

fun checkFlex (): unit =
    let fun check1 (tv,r) =
            (case !tv
               of OPEN{kind=FLEX _,...} =>
                  (err region COMPLAIN
			  "unresolved flex record (hidden)"
		       (fn ppstrm =>
			     (PPType.resetPPType();
			      PP.newline ppstrm;
			      PP.string ppstrm "type: ";
			      ppType ppstrm (VARty(tv)))))
                | INSTANTIATED _ => ()
                | _ => bug "checkFlex")
    in if anyErrors () then ()
       else app check1 (!flexTyVars)
    end

(* managing source locations (srcloc = SourceMap.region) *)

val nullRegion = SourceMap.nullRegion

(* translating a marked type to its origin srcloc *)
(* We need to worry about immediately nested MARKty's, where a wider
 * region is wrapped immediately around a narrower one. Hence the
 * first rule. *)
fun tyToLoc (MARKty(t as MARKty _,region)) = tyToLoc t
  | tyToLoc (MARKty(ty,region)) = region
  | tyToLoc _ = SourceMap.nullRegion

                    fun unifyErr{ty1,name1,ty2,name2,message=m,region,kind,kindname,phrase} =
                        (unifyTy(ty1,ty2,tyToLoc ty1,tyToLoc ty2); true) handle Unify(mode) =>
                            (err region COMPLAIN (message(m,mode))
                             (fn ppstrm => 
                              (PPType.resetPPType();
                               let val len1= size name1 
                                   val len2= size name2
                                   val spaces = "                                   "
                                   val pad1= substring(spaces,0,Int.max(0,len2-len1))
                                   val pad2= substring(spaces,0,Int.max(0,len2-len1))
                                   val m = if m="" then name1 ^ " and " ^ name2 ^ " don't agree"
                                           else m
                               in if name1="" then ()
                                  else (PP.newline ppstrm; PP.string ppstrm (name1 ^ ": " ^ pad1);
                                        ppType ppstrm ty1); 
                                      if name2="" then ()
                                      else (PP.newline ppstrm; PP.string ppstrm (name2 ^ ": " ^ pad2);
                                            ppType ppstrm ty2);
                                          if kindname="" then ()
                                          else (PP.newline ppstrm;
                                                PP.string ppstrm("in "^kindname^":");
                                                PP.break ppstrm {nsp=1,offset=2}; 
                                                kind ppstrm (phrase,!printDepth));
                                                ppModeErrorMsg ppstrm mode
                               end));
                             false)
                             

                    (* Printing a semiunification problem *)

                    val ppTypelist = PPTL.pptypelist env
                    val ppIneqlist = PPTL.ppineqlist env
                    val g = PP.with_pp(ErrorMsg.defaultConsumer())

                    fun nameprint name = (g (fn ppstream => ppSym ppstream name); print ":")
                    and typprint typ = (g (fn ppstream => ppType ppstream typ); print "\n")
                    and inpr ilist   = (g (fn ppstream => ppIneqlist ppstream ilist))
                    and lpr tlist    = (g (fn ppstream => ppTypelist ppstream tlist))
                    and rvbpr dec    = (g (fn ppstream => ppDec' ppstream dec))
                    and rulepr exp   = (g (fn ppstream => ppRule ppstream (exp,!printDepth)))
                    and letpr exp    = (g (fn ppstream => ppExp ppstream (exp,!printDepth)))
                    and monopr monoConstr = 
                        let 
                            val monos = (SU.monoConstraintsAsIneqns monoConstr)
                        in 
                            if length monos > 0 then 
                                (print "the monomorphic vars (instantiated):\n";
                                 inpr monos)
                            else ()
                        end

                    fun revadd (a::acc) list = revadd acc (a::list)
                      | revadd [] list = list

                    (* Global variables for semiunification: *)

                    val rulebound = ref([] : ty list)             (* types in lambda-assumptions *)
                    val recbound  = ref([] : VarCon.var list)     (* indiv.recvars during recDec *)
                    val semiprob  = ref([] : SU.ineq list)        (* semiunfication constraints  *)
                    val monoConstraints 
                        = ref([] : SU.monoconstraint list)        (* monomorphic tyvars *)
                    val topprob   = ref true
                    val eqcounter = ref 0                         (* inequation counter - var occ.no *)
                    val printSolvedIneqns = ref true

                    (* Viewing intermediate steps of the semiunification solving process *)

                    fun showIneqns (ineqnsL,ineqnsR) thestring =
                        (print (thestring^" print? ");
                         let 
                             val (SOME answer) = TextIO.inputLine(TextIO.stdIn)
                         in
                             if answer = "y\n" 
                                 then (inpr (revadd ineqnsR ineqnsL);
                                       monopr (!monoConstraints);
                                       print "\n";
                                       (ineqnsL,ineqnsR)) 
                             else if answer = "stop\n" then 
                                 (viewsemi := 1; (ineqnsL,ineqnsR)) 
                                  else (ineqnsL,ineqnsR)
                         end)

                    val _ = SU.show := showIneqns

                    fun checkvarpr varname semiprob ineqnsByCopying = 
                        if (!viewsemi) > (!(# Var showsemi))
                            then
                                (print ("Show var case for occurrence of: " ^ varname ^ " ? ");
                                 let 
                                     val (SOME answer) = TextIO.inputLine(TextIO.stdIn)
                                 in (if answer = "y\n" then 
                                         (print "\nnew inequations by copying:\n";
                                          inpr ineqnsByCopying;
                                          print "other inequations: \n";
                                          inpr (!semiprob); 
                                          print "\n") 
                                     else (if answer = "stop\n" then viewsemi := 1 else ()))
                                 end)
                        else ()

                    fun checkrulepr1 therule pty semiprob =
                        if (!viewsemi) > (!(# Rule showsemi)) then
                            (print "Show rule case for: \n";
                             (rulepr therule); 
                             print " ? ";
                             let val (SOME answer) = TextIO.inputLine(TextIO.stdIn) 
                             in if answer = "y"^"\n" then
                                 (print "\n"; print "the pattern type is: \n"; 
                                  typprint pty;
                                  print "\nthe inequations are: \n";
                                  inpr (!semiprob);
                                  monopr (!monoConstraints);
                                  print "\n";
                                  true)
                                else if answer = "stop"^"\n" then 
                                    (viewsemi := 1; false)
                                     else false
                             end)
                        else false

                    and checkrulepr2 printAfterRule semiprob =
                        if printAfterRule then 
                            (print "The inequations after typing the rule are: \n";
                             inpr (!semiprob);
                             monopr (!monoConstraints);
                             print "\n")
                        else ()

                    fun checkletpr1 thelet semiprob = 
                        if (!viewsemi) > (!(# Let showsemi)) then
                            (print "Show let case for: \n";
                             letpr thelet;
                             print " ? ";
                             let val (SOME answer) = TextIO.inputLine(TextIO.stdIn) 
                             in (if answer = "y\n" 
                                     then (print "Inequations before typing the let-expression: \n";
                                           inpr (!semiprob);
                                           monopr (!monoConstraints);
                                           print "\n";
                                           true)
                                 else false)
                             end)
                        else false

                    and checkletpr2 printAfterLet semiprob = 
                        if printAfterLet then 
                            (print "Inequations after typing the let-expression:\n";
                             inpr (!semiprob);
                             monopr (!monoConstraints);
                             print "\n")
                        else ()

                    fun checkrvbpr1 rvbs semiprob monoConstraints = 
                        if (!viewsemi) > (!(# Valrec showsemi)) 
                            then (print "Show recursive value case for:\n";
                                  rvbpr (VALRECdec (rvbs));
                                  print " ? ";
                                  let val (SOME answer) = TextIO.inputLine(TextIO.stdIn) 
                                  in (if answer = "y\n" then 
                                          (print "\nInequations before solving: \n";
                                           inpr (!semiprob);
                                           monopr (!monoConstraints);
                                           (if List.length (!semiprob) > 0 then
                                                (print "\nStep through solving the inequations? ";
                                                 let val (SOME answer) = TextIO.inputLine(TextIO.stdIn)
                                                 in (if answer = "y\n" then 
                                                         (# Step showsemi) := (!(# Valrec showsemi))
                                                     else (# Step showsemi) := (!viewsemi))
                                                 end)
                                            else ());
                                           true)
                                      else false) 
                                  end)
                        else false

                    and checkrvbpr2 solved semiprob monoConstraints =
                        if solved = true then 
                            (print "Inequations after solving: \n";
                             inpr (!semiprob);
                             monopr (!monoConstraints);
                             print "\n")
                        else ()


                    (* Updating the list of rulebound tyvars *)

                    fun rbupdate ty = case (prune ty) of 
                        CONty(tyc,args) => app rbupdate args
                      | VARty(ref(OPEN{kind=FLEX(fields),...}))
                            => app (rbupdate o #2) fields
                      | v as VARty(ref(OPEN{kind=META,...}))
                            => (rulebound := (v::(!rulebound)))
                      | v as (VARty(tvinfo)) (* UBOUND | OVLDI | OVLDW | LBOUND *)
                            => (rulebound := (v::(!rulebound)))
                      | _ => () 
                    and isRulebound ty = 
                        let fun there x (y::z) = if equalType(x,y) then true else there x z
                              |  there _ [] = false
                        in there ty (!rulebound) 
                        end

(* For polymorphic recursion, expType needs to know if an individual variable is 
 mono- or poly-bound. Since VALvar{typ,name,access} does not have this attribute,
 to test the property we stack the rec-bound vars and pop after recdecs).
 *) 

fun polybound v = case v of 
    VALvar{typ=ref(POLYty _),...} => true        (* applied occurrences of dec-vars *)
  | VALvar{typ=ref(VARty(ref(OPEN{kind=META,...}))),...} =>
	member v (!recbound)  (* occurrences of rec-dec vars in defining expression *)
  | _ => false 
and member x [] = false
  | member x (y::ys) = if eqVar(x,y) then true else member x ys
and eqVar(VALvar{access=accx,...},VALvar{access=accy,...}) = (accx = accy) 
  | eqVar(_,_) = false

(* To type a variable occurrence, copy the (body of) the assumed type *) 

fun copyTy(ty) =
    let val copymap = ref([]:(ty * ty) list)

        fun fetchCopy ty =
	    let fun find [] = raise NotThere
		  | find((ty1,ty2)::rest) = if equalType(ty,ty1) then ty2 
                                            else find rest
            in find(!copymap)
	    end

        fun fetchRulebound ty = if isRulebound ty then ty else raise NotThere

        fun copy(ty) = case prune(ty) 
            of VARty(tv as ref(OPEN{depth=d,eq=e,kind=k})) =>
                (case k 
                     of META => 
                         (fetchCopy(VARty(tv)) handle NotThere =>  
                             fetchRulebound(VARty(tv)) handle NotThere =>
                                 (* NOTE 1: although the rulebound list of the occurrence of 
                                  indiv.var label is bigger than monoConstraints(label,_), 
                                  ty cannot contain tyvars of rulebound-monoconstr. *)
                                 if (d=infinity orelse d=0) then VARty(tv)
                                 else let val tv' = ref(!tv)
                                      in (copymap := (VARty(tv),VARty(tv'))::(!copymap);
                                          VARty(tv'))
                                      end)                           
                   | FLEX(fields) =>
                             let fun f (lab,ty) = (lab,copy ty) 
                             in (tv := OPEN{kind=FLEX(map f fields),depth=d,eq=e};
                                 VARty(tv))
                             end)
          | VARty(tv as ref(UBOUND{...})) => VARty(tv)
          | CONty(tyc,args) => CONty(tyc, map copy args) 
          | POLYty{sign=polysign,tyfun=tyfun} => POLYty{sign=polysign,tyfun=tyfun} (* ??? *)
          | IBOUND(n) => IBOUND(n)
          | WILDCARDty => WILDCARDty
          | UNDEFty => UNDEFty
          | tp => tp
    in 
        (copy(ty),!copymap)
    end

fun copy label ty =  
    let 
        val _ = SU.compress rulebound   
        (* NOTE 2: need only compress monoconstraints(label), but see NOTE 1 *)
        val (ty',pairs) = copyTy(ty)
        val _ = case pairs of nil => () | (p::ps) => (eqcounter := (!eqcounter) + 1)
        val ineqnsByCopying = 
            (map (fn (x,y) => SU.ineq(label,!eqcounter,x,y)) pairs)
        val (SU.mylab(_,var)) = label
        val _ = checkvarpr (Symbol.name var) semiprob ineqnsByCopying 
        val _ = semiprob := revadd ineqnsByCopying (!semiprob)
    in
        ty'
    end

val _ = debugmsg (">>decType: toplev = " ^ Bool.toString toplev)
val _ = ppDecDebug(">>decType: dec = ",dec)

fun generalizeTy(VALvar{typ,path,btvs,...}, userbound: tyvar list,
		 occ:occ, generalize: bool, region) : tyvar list =
    let val _ = debugmsg (">>>generalizeTy: "^SymPath.toString path)
	val _ = debugmsg ("userbound: ")
        val _ = debugmsg ("generalize: "^Bool.toString generalize)
        val _ = debugmsg ("occ: "^Int.toString(lamdepth occ)^", "^Bool.toString(toplevel occ))
	val _ = List.app ppTyvarDebug userbound

	val failure = ref false
	val mkDummy = if toplevel occ
	              then TypesUtil.dummyTyGen()
		      else mkDummy0 (* shouldn't be called *)

	val index = ref 0  (* counts number of type variables bound *)
	fun next() = !index before (index := !index + 1)
	val sign = ref([]: Types.polysign)
	fun localUbound tv = List.exists (fn tv' => eqTyvar(tv,tv')) userbound

	(* menv: a reference to an association list environment mapping
	 *   generalized tyvars to the corresponding IBOUND type.
	 * ASSERT: there are no duplicate tyvars in domain of menv. *)
	val menv = ref([]: (tyvar*ty) list)
	fun lookup tv =
	    let fun find [] = raise NotThere
		  | find((tv',ty)::rest) = if eqTyvar(tv,tv') then ty
							      else find rest
	     in find(!menv)
	    end
	fun bind(tv,ty) = menv := (tv,ty) :: !menv

	fun gen(ty) =
	    case ty
	     of VARty(ref(INSTANTIATED ty)) => gen ty
	      | VARty(tv as ref(OPEN{depth,eq,kind})) =>
		  (case kind
		     of FLEX[(lab,_)] =>
                         if ((depth > lamdepth occ) andalso
                             (generalize orelse (toplevel occ)))
                            orelse ((toplevel occ) andalso (depth=0))
                         then
			   (err region COMPLAIN (String.concat
			     ["unresolved flex record\n\
			      \   (can't tell what fields there are besides #",
			      Symbol.name lab, ")"])
			    nullErrorBody;
                            tv := INSTANTIATED WILDCARDty;
			    WILDCARDty)
                         else ty
		      | FLEX _ =>
                         if ((depth > lamdepth occ) andalso
                             (generalize orelse (toplevel occ)))
                            orelse ((toplevel occ) andalso (depth=0))
                         then
  			   (err region COMPLAIN
			        "unresolved flex record (need to know the \
			        \names of ALL the fields\n in this context)"
			    (fn ppstrm =>
			       (PPType.resetPPType();
				PP.newline ppstrm;
				PP.string ppstrm "type: ";
				ppType ppstrm ty));
                            tv := INSTANTIATED WILDCARDty;
			    WILDCARDty)
                         else ty
		      | META =>
			  if depth > lamdepth occ
			  then if generalize then
				  lookup tv handle NotThere =>
				    let val new = IBOUND(next())
				     in sign := eq :: !sign;
				        bind(tv,new);
					new
				    end
			       else (if toplevel occ
				     then let val new = mkDummy()
					   in failure := true;
                                              tv := INSTANTIATED new;
					      new
					  end
				     else (if !ElabControl.valueRestrictionLocalWarn
					   then err region WARN
				             ("type variable not generalized\
                                              \ in local decl (value restriction): "
                                              ^ (tyvarPrintname tv))
				             nullErrorBody
					   else ();
					   (* reset depth to prevent later
					      incorrect generalization inside
					      a lambda expression. See typechecking
					      test 5.sml *)
					   tv := OPEN{depth = lamdepth occ,
						      eq = eq, kind = kind};
					   ty))
			  else if toplevel occ andalso depth = 0
			   (* ASSERT: failed generalization at depth 0.
			      see bug 1066. *)
			    then lookup tv handle NotThere =>
				 let val new = mkDummy()
				  in failure := true;
                                     tv := INSTANTIATED new;
				     new
				 end
			  else ty) (* raise SHARE *)
	      | VARty(tv as ref(UBOUND{name,depth,eq})) =>
		 (debugmsg ("UBOUND:" ^Symbol.name name);
		  if localUbound tv
		  then (debugmsg "is local";
		       if depth > lamdepth occ andalso generalize
		       then (debugmsg "is generalized";
			     lookup tv handle NotThere =>
			      let val new = IBOUND(next())
			       in sign := eq :: !sign;
				  bind(tv,new);
				  new
			      end)
		       else (err region COMPLAIN
			     ("explicit type variable cannot be \
			       \generalized at its binding \
			       \declaration: " ^
			       (tyvarPrintname tv))
			      nullErrorBody;
			     tv := INSTANTIATED WILDCARDty;
			     WILDCARDty))
		  else (debugmsg "is not local"; ty))
	      | VARty(ref(OVLDV _ | OVLDI _ | OVLDW _)) => ty
	      | CONty(tyc,args) => CONty(tyc, map gen args) (*shareMap*)
	      | WILDCARDty => WILDCARDty
	      | MARKty(ty, region) =>
	      	let val () = ppTypeDebug (">> Markty", ty)
		in gen ty
		end
	      | _ => bug "generalizeTy -- bad arg"

	val _ = ppTypeDebug (">>gen: before: ",!typ)
	val ty = gen(!typ)
	val _ = ppTypeDebug (">>gen: after: ",ty)

        val generalizedTyvars = map #1 (rev(!menv))

        (* a hack to eliminate all user bound type variables --zsh *)
	(* ZHONG?: is this still necessary? [dbm] *)
        (* DBM: are ubound tyvars redefined by indexBoundTyvars in
         * generalizePat below? *)
	fun elimUbound(tv as ref(UBOUND{depth,eq,...})) =
              (tv := OPEN{depth=depth,eq=eq,kind=META})
          | elimUbound _ = ()

        (* turn ubound tyvars into ordinary META tyvars *)
        val _ = app elimUbound generalizedTyvars

     in if !failure andalso !ElabControl.valueRestrictionTopWarn
	  then err region WARN
	        "type vars not generalized because of\n\
                 \   value restriction are instantiated to dummy types (X1,X2,...)"
		nullErrorBody
          else ();
	debugmsg "generalizeTy returning";
	typ := (if !index > 0 then
                   POLYty{sign = rev(!sign),
		          tyfun = TYFUN{arity=(!index),body=ty}}
               else ty);
	btvs := generalizedTyvars;
	generalizedTyvars  (* return the tyvars that were generalized *)
    end

  | generalizeTy _ = bug "generalizeTy - bad arg"

fun generalizePat(pat: pat, userbound: tyvar list, occ: occ, tdepth, 
                  generalize: bool, region) =
    let val tvs : tyvar list ref = ref []
	fun union ([],tvs) = tvs
	  | union (tv::rest,tvs) = if List.exists (fn tv' => (tv = tv')) tvs then union(rest,tvs)
				   else tv :: (union(rest,tvs))
        fun gen(VARpat v) =
	      tvs := union(generalizeTy(v,userbound,occ,generalize,region), !tvs)
	  | gen(RECORDpat{fields,...}) = app (gen o #2) fields
	  | gen(APPpat(_,_,arg)) = gen arg
	  | gen(CONSTRAINTpat(pat,_)) = gen pat
	  | gen(LAYEREDpat(varPat,pat)) = (gen varPat; gen pat)
          | gen(MARKpat(pat,reg)) = gen pat
	  | gen _ = ()
     in gen pat; !tvs
    end

fun applyType(ratorTy: ty, randTy: ty) : ty =
  let val resultType = mkMETAty()
   in unifyTy(ratorTy, (randTy --> resultType), tyToLoc ratorTy, tyToLoc randTy);
      resultType
  end

fun stripMarksVar (MARKpat(p as VARpat _, reg)) = p
  | stripMarksVar (MARKpat(p,reg)) = stripMarksVar p
  | stripMarksVar (CONSTRAINTpat (p, ty)) =
      CONSTRAINTpat(stripMarksVar p, ty)
  | stripMarksVar p = p

fun patType(pat: pat, depth, region) : pat * ty =
    case pat
      of WILDpat => (pat,mkMETAtyBounded depth)
       | MARKpat(p,region') => patType(p,depth,region')
       | VARpat(VALvar{typ as ref UNDEFty,...}) =>
	      (typ := mkMETAtyBounded depth; (pat,MARKty(!typ, region)))
			             (* multiple occurrence due to or-pat *)
       | VARpat(VALvar{typ, ...}) => (pat, MARKty(!typ, region)) 
       | NUMpat(src, {ival, ty}) => (pat, oll_push(ival, src, ty, err region))
       | STRINGpat _ => (pat,MARKty(stringTy, region))
       | CHARpat _ => (pat,MARKty(charTy, region))
       | RECORDpat{fields,flex,typ} =>
	   (* fields assumed already sorted by label *)
	   let fun fieldType(lab,pat') =
                 let val (npat,nty) = patType(pat',depth,region)
                  in ((lab,npat), (lab,nty))
                 end
               val (fields',labtys) = mapUnZip fieldType fields
               val npat = RECORDpat{fields=fields',flex=flex,typ=typ}
	    in if flex
	       then let val tv = mkTyvar(mkFLEX(labtys,depth))
                        val ty = VARty(tv)
		     in registerFlex(tv,region);
                        typ := ty; (npat,ty)
		    end
	       else (npat,MARKty(recordTy(labtys), region))
	   end
       | VECTORpat(pats,_) =>
          (let val (npats,ntys) =
                     mapUnZip (fn pat => patType(pat,depth,region)) pats
               val nty =
	       foldr (fn (a,b) => (unifyTy(a, b, tyToLoc a, tyToLoc b); b))
		     (mkMETAtyBounded depth) ntys
            in (VECTORpat(npats,nty),
	    	MARKty(CONty(vectorTycon,[nty]), region))
           end handle Unify(mode) => (
	     err region COMPLAIN
		 (message("vector pattern type failure",mode)) nullErrorBody;
	     (pat,WILDCARDty)))
       | ORpat(p1, p2) =>
           let val (p1, ty1) = patType(p1, depth, region)
  	       val (p2, ty2) = patType(p2, depth, region)
	    in unifyErr{ty1=ty1,ty2=ty2,name1="expected",name2="found",
			message="or-patterns do not agree",region=region,
			kind=ppPat,kindname="pattern",phrase=pat};
	       (ORpat(p1, p2), MARKty(ty1, region))
	   end
       | CONpat(dcon as DATACON{typ,...},_) =>
           let val (ty, insts) = instantiatePoly typ
               (* the following unification is used to set the correct depth information
                * for the type variables in ty. (ZHONG)  It cannot fail.
                *)
               val nty = mkMETAtyBounded depth
               val _ = unifyTy(nty, ty, tyToLoc nty, tyToLoc ty)
            in (CONpat(dcon, insts), MARKty(ty, region))
           end
       | APPpat(dcon as DATACON{typ,rep,...},_,arg) =>
	   let val (argpat,argty) = patType(arg,depth,region)
               val (ty1,ndcon) = case rep
                                  of DA.REF => (refPatType,refNewDcon dcon)
                                   | _ => (typ,dcon)
               val (ty2,insts) = instantiatePoly ty1
               val npat = APPpat(ndcon,insts,argpat)
            in (npat,MARKty(applyType(ty2,argty), region))
	       handle Unify(mode) =>
		(err region COMPLAIN
                  (message("constructor and argument do not agree in pattern",mode))
		  (fn ppstrm =>
		   (PPType.resetPPType();
		    PP.newline ppstrm;
		    PP.string ppstrm "constructor: ";
		    ppType ppstrm typ; PP.newline ppstrm;
		    PP.string ppstrm "argument:    ";
		    ppType ppstrm argty; PP.newline ppstrm;
		    PP.string ppstrm "in pattern:"; PP.break ppstrm {nsp=1,offset=2};
		    ppPat ppstrm (pat,!printDepth)));
		 (pat,WILDCARDty))
	   end
       | CONSTRAINTpat(pat',ty) =>
	   let val (npat,patTy) = patType(pat',depth,region)
	    in if unifyErr{ty1=patTy,name1="pattern",ty2=ty,name2="constraint",
                           message="pattern and constraint do not agree",
                           region=region,kind=ppPat,kindname="pattern",phrase=pat}
		then (CONSTRAINTpat(npat,MARKty(ty,region)),MARKty(ty,region))
		else (pat,WILDCARDty)
	   end
       | LAYEREDpat(vpat,pat') =>
	   (case stripMarksVar vpat
              of VARpat(VALvar{typ,...}) =>
		 let val (npat,patTy) = patType(pat',depth,region)
		     val _ = (typ := patTy)
		  in (LAYEREDpat(vpat,npat),MARKty(patTy, region))
		 end
	       | (cpat as CONSTRAINTpat(VARpat(VALvar{typ,...}),ty)) =>
		 let val (npat,patTy) = patType(pat',depth,region)
		  in if unifyErr{ty1=patTy,name1="pattern",ty2=ty,name2="constraint",
				 message="pattern and constraint do not agree",
				 region=region,kind=ppPat,kindname="pattern",phrase=pat}
		     then (typ := ty; (LAYEREDpat(cpat,npat),MARKty(ty, region)))
		     else (pat,WILDCARDty)
		 end
               | _ => bug "patType -- missing case in LAYEREDpat")
       | p => bug "patType -- unexpected pattern"

fun expType(exp: exp, occ: occ, tdepth: DI.depth, region) : exp * ty =
let fun boolUnifyErr { ty, name, message } =
	unifyErr { ty1 = ty, name1 = name, ty2 = boolTy, name2 = "",
		   message = message, region = region, kind = ppExp,
		   kindname = "expression", phrase = exp }
    fun boolshortcut (con, what, e1, e2) =
	let val (e1', t1) = expType (e1, occ, tdepth, region)
	    val (e2', t2) = expType (e2, occ, tdepth, region)
	    val m = String.concat ["operand of ", what, " is not of type bool"]
	in
	    if boolUnifyErr { ty = t1, name = "operand", message = m }
	    andalso boolUnifyErr { ty = t2, name = "operand", message = m }
	    then (con (e1', e2'), MARKty(boolTy, region))
	    else (exp, WILDCARDty)
	end
in
     case exp
      of (* VARexp(r as ref(v as VALvar{typ, ...}), _) =>
	   let val (ty, insts) = instantiatePoly(!typ)
	    in (VARexp(r, insts), MARKty(ty, region))
	   end
       | *)
         VARexp(r as ref(VALvar{typ, ...}),_) => 
           let 
               val (SU.mylab(_,lab)) = Findvars.find_var_var(!r)
               val varname = Symbol.name lab
               val (ty1,insts) = instantiatePoly(!typ)
               val ty = if (!ElabControl.oldchecker) then ty1 
                        else if polybound (!r) 
                                 then 
                                       (copy (Findvars.find_var_var(!r)) ty1)
                             else ty1 
	    in (VARexp(r, insts), MARKty(ty, region))  (* should be insts[copied tyvars] ? *)
	   end
       | VARexp(r as ref(OVLDvar _),_) =>
 	   (exp, olv_push (r, region, err region))
       | VARexp(r as ref ERRORvar, _) => (exp, WILDCARDty)
       | CONexp(dcon as DATACON{typ,...},_) =>
           let val (ty,insts) = instantiatePoly typ
            in (CONexp(dcon, insts), MARKty(ty, region))
           end
       | NUMexp(src, {ival, ty}) => (exp, oll_push(ival, src, ty, err region))
(* REAL32: overload real literals *)
       | REALexp _ => (exp,MARKty(realTy, region))
       | STRINGexp _ => (exp,MARKty(stringTy, region))
       | CHARexp _ => (exp,MARKty(charTy, region))
       | RECORDexp fields =>
           let fun h(l,exp') =
                    let val (nexp,nty) = expType(exp',occ,tdepth,region)
                     in ((l,nexp),(l,nty))
                    end
               fun extract(LABEL{name,...},t) = (name,t)
               val (fields',tfields) = mapUnZip h fields
               val rty = map extract (sortFields tfields)
            in (RECORDexp fields',MARKty(recordTy(rty), region))
           end
       | SELECTexp (l, e) =>
           let val (nexp, nty) = expType(e, occ, tdepth, region)
               val res = mkMETAty ()
               val labtys = [(EU.labsym l, res)]
               val tv = mkTyvar(mkFLEX(labtys,infinity))
               val pt = VARty tv
               val _ = registerFlex(tv,region)
            in (unifyTy(pt, nty, tyToLoc pt, tyToLoc nty);
		(SELECTexp(l, nexp), MARKty(res, region)))
               handle Unify(mode) =>
                 (err region COMPLAIN
                  (message("selecting a non-existing field from a record",mode))
                  (fn ppstrm =>
                   (PPType.resetPPType();
                    PP.newline ppstrm;
                    PP.string ppstrm "the field name: ";
                    (case l of LABEL{name,...} => ppSym ppstrm name);
                    PP.newline ppstrm;
                    PP.string ppstrm "the record type:    ";
                    ppType ppstrm nty; PP.newline ppstrm;
                    PP.string ppstrm "in expression:";
                    PP.break ppstrm {nsp=1,offset=2};
                    ppExp ppstrm (exp,!printDepth)));
                    (exp, WILDCARDty))
           end
       | VECTORexp(exps,_) =>
          (let val (exps',nty) = mapUnZip (fn e => expType(e,occ,tdepth,region)) exps
               val vty = foldr (fn (a,b) => (unifyTy(a,b,tyToLoc a,tyToLoc b); b))
                               (mkMETAty()) nty
            in (VECTORexp(exps',vty), MARKty(CONty(vectorTycon,[vty]), region))
           end handle Unify(mode) =>
	   (err region COMPLAIN
	     (message("vector expression type failure",mode))
             nullErrorBody; (exp,WILDCARDty)))
       | SEQexp exps =>
	   let fun scan nil = (nil,unitTy)
	         | scan [e] =
                     let val (e',ety) = expType(e,occ,tdepth,region)
                      in ([e'],ety)
                     end
		 | scan (e::rest) =
                     let val (e',_) = expType(e,occ,tdepth,region)
                         val (el',ety) = scan rest
                      in (e'::el',ety)
                     end
               val (exps',expty) = scan exps
            in (SEQexp exps',MARKty(expty, region))
	   end
       | APPexp(rator, rand) =>
	   let val (rator',ratorTy) = expType(rator,occ,tdepth,region)
	       val (rand',randTy) = expType(rand,occ,tdepth,region)
               val exp' = APPexp(rator',rand')
	    in (exp',applyType(ratorTy,MARKty(randTy, region)))
	       handle Unify(mode) =>
	       let val ratorTy = prune ratorTy
		   val reducedRatorTy = headReduceType ratorTy
		in PPType.resetPPType();
		   if isArrowType(reducedRatorTy)
		   then (err region COMPLAIN
			  (message("operator and operand do not agree",mode))
			  (fn ppstrm =>
			   (PP.newline ppstrm;
			    PP.string ppstrm "operator domain: ";
			    ppType ppstrm (domain reducedRatorTy);
			    PP.newline ppstrm;
			    PP.string ppstrm "operand:         ";
			    ppType ppstrm randTy; PP.newline ppstrm;
			    PP.string ppstrm "in expression:";
			    PP.break ppstrm {nsp=1,offset=2};
			    ppExp ppstrm (exp,!printDepth);
			    ppModeErrorMsg ppstrm mode));
			 (exp,WILDCARDty))
		   else (err region COMPLAIN
			  (message("operator is not a function",mode))
			  (fn ppstrm =>
			    (PP.newline ppstrm;
			     PP.string ppstrm "operator: ";
			     ppType ppstrm (ratorTy); PP.newline ppstrm;
			     PP.string ppstrm "in expression:";
			     PP.break ppstrm {nsp=1,offset=2};
			     ppExp ppstrm (exp,!printDepth);
			     ppModeErrorMsg ppstrm mode));
			 (exp,WILDCARDty))
	       end
	   end
       | CONSTRAINTexp(e,ty) =>
	   let val (e',ety) = expType(e,occ,tdepth,region)
	    in if unifyErr{ty1=ety,name1="expression", ty2=ty, name2="constraint",
			message="expression does not match constraint",
			region=region,kind=ppExp,kindname="expression",
			phrase=exp}
		then (CONSTRAINTexp(e',MARKty(ty, region)),
			MARKty(ty, region))
		else (exp,WILDCARDty)
	   end
       | HANDLEexp(e, (rules, _)) =>
	   let val (e',ety) = expType(e,occ,tdepth,region)
	       and (rules',rty,hty) = matchType (rules, occ, region)
               val exp' = HANDLEexp(e', (rules', rty))
	    in (unifyTy(hty, exnTy --> ety, tyToLoc hty, tyToLoc exnTy);
		(exp', MARKty(ety, region)))
	       handle Unify(mode) =>
		 (if unifyErr{ty1=domain(prune hty), name1="handler domain",
			     ty2=exnTy, name2="",
			     message="handler domain is not exn",
			     region=region,kind=ppExp,kindname="expression",
			     phrase=exp}
		     then unifyErr{ty1=ety, name1="body",
				   ty2=range(prune hty), name2="handler range",
				   message="expression and handler do not agree",
				   region=region,
				   kind=ppExp,kindname="expression",phrase=exp}
		     else false;
		  (exp,WILDCARDty))
	   end
       | RAISEexp(e,_) =>
	   let val (e',ety) = expType(e,occ,tdepth,region)
               val newty = mkMETAty()
	    in unifyErr{ty1=ety, name1="raised", ty2=exnTy, name2="",
			message="argument of raise is not an exception",
			region=region,kind=ppExp,kindname="expression",phrase=exp};
	       (RAISEexp(e',newty),MARKty(newty, region))
	   end
       | LETexp(d,e) => 
             if (!ElabControl.oldchecker) then
                 let val d' = decType0(d,LetDef(occ),tdepth,region)
                     val (e',ety) = expType(e,occ,tdepth,region)
                  in (LETexp(d',e'),MARKty(ety,region)) 
                 end
             else let val printAfterLet = (checkletpr1 (LETexp(d,e)) semiprob)
                      val d' = decType0(d,LetDef(occ),tdepth,region)
                      val (e',ety) = expType(e,occ,tdepth,region)
                   in 
                       (checkletpr2 printAfterLet semiprob;
                       (LETexp(d',e'),MARKty(ety,region)))
                   end

       | CASEexp(e,rules,isMatch) =>
	   let val (e',ety) = expType(e,occ,tdepth,region)
	       val (rules',_,rty) = matchType(rules,occ,region)
               val exp' = CASEexp(e',rules', isMatch)
	    in (exp',MARKty(applyType(rty,ety), region))
	       handle Unify(mode) =>
	       (if isMatch then
		    unifyErr{ty1=domain rty, name1="rule domain",
			     ty2=ety, name2="object",
			     message="case object and rules do not agree",
			     region=region,kind=ppExp,kindname="expression",phrase=exp}
                else
                 let val decl = case rules
                                 of (RULE(pat,_))::_ =>
				    VB{pat=pat,exp=exp,tyvars=ref[],boundtvs=[]}
                                  | _ => bug "unexpected rule list 456"
		  in unifyErr{ty1=domain rty, name1="pattern",
			      ty2=ety, name2="expression",
			      message="pattern and expression in val dec do not agree",
			      region=region,kind=ppVB,kindname="declaration",
			      phrase=decl}
                 end;
	        (exp,WILDCARDty))
	   end
		 (* this causes case to behave differently from let, i.e.
		    bound variables do not have generic types *)
       | IFexp { test, thenCase, elseCase } =>
	   let val (test', tty) = expType (test,occ,tdepth,region)
	       val (thenCase', tct) = expType (thenCase, occ, tdepth, region)
	       val (elseCase', ect) = expType (elseCase, occ, tdepth, region)
	   in
	       if boolUnifyErr
		      { ty = tty, name = "test expression",
			message="test expression in if is not of type bool" }
	       andalso
	          unifyErr { ty1 = tct, name1 = "then branch",
			     ty2 = ect, name2 = "else branch",
			     message="types of if branches do not agree",
			     region = region, kind = ppExp,
			     kindname = "expression", phrase = exp }
	       then
		   (IFexp { test = test', thenCase = thenCase',
			    elseCase = elseCase' },
		    MARKty(tct, region))
	       else
		   (exp, WILDCARDty)
	   end
       | ANDALSOexp (e1, e2) =>
	   boolshortcut (ANDALSOexp, "andalso", e1, e2)
       | ORELSEexp (e1, e2) =>
	   boolshortcut (ORELSEexp, "orelse", e1, e2)
       | WHILEexp { test, expr } =>
	   let val (test', tty) = expType (test, occ, tdepth, region)
	       val (expr', _) = expType (expr, occ, tdepth, region)
	   in
	       if boolUnifyErr { ty = tty, name = "test expression",
				 message = "test expression in while is not of type bool" }
	       then
		   (WHILEexp { test = test', expr = expr' }, MARKty(unitTy, region))
	       else
		   (exp, WILDCARDty)
	   end
       | FNexp(rules,_) =>
           let val (rules',ty,rty) = matchType(rules,occ,region)
            in (FNexp(rules',ty),MARKty(rty, region))
           end
       | MARKexp(e,region) =>
           let val (e',et) = expType(e,occ,tdepth,region)
            in (MARKexp(e',region),MARKty(et, region))
           end
end

and ruleType(RULE(pat,exp),occ,region) =  
    if (!ElabControl.oldchecker) then    
        let val occ = Abstr occ
            val (pat',pty) = patType(pat,lamdepth occ,region)
            val (exp',ety) = expType(exp,occ,tdepth,region)
        in (RULE(pat',exp'),pty,pty --> ety)
        end
    else
        let val occ = Abstr occ
            val (pat',pty) = patType(pat,lamdepth occ,region)
            val printAfterRule = checkrulepr1 (RULE(pat,exp)) pty semiprob
            val oldrulebound = (!rulebound) 
            val _ = rbupdate pty
            val (exp',ety) = expType(exp,occ,tdepth,region)
        in 
            (rulebound := oldrulebound);
            (checkrulepr2 printAfterRule semiprob);
            (RULE(pat',exp'),pty,pty --> ety)
        end

and matchType(l,occ,region) =
    case l
      of [] => bug "empty rule list in typecheck.matchType"
       | [rule] =>
	    let val (rule0,argt,rty) = ruleType(rule,occ,region)
	     in ([rule0],argt,rty)
	    end
       | rule::rest =>
	    let val (rule0,argt,rty) = ruleType(rule,occ,region)
		fun checkrule rule' =
		   let val (rule1,argt',rty') = ruleType(rule',occ,region)
		    in unifyErr{ty1=rty,ty2=rty', name1="earlier rule(s)",
				name2="this rule",
				message="types of rules do not agree",
				region=region,
				kind=ppRule,kindname="rule",phrase=rule'};
		       rule1
		   end
	     in (rule0::(map checkrule rest),argt,rty)
	    end

and decType0(decl,occ,tdepth,region) : dec =
    let 
        val labels = Findvars.find_dec_vars(decl)  
        fun updateMonoConstraints labs =            
             let 
                 val _ = SU.compress rulebound
                 val node = ref (!rulebound)  (* share these for all labs *)
             in  
                 monoConstraints := 
                 (map (fn lb => (lb,node)) labs) @ (!monoConstraints)
             end
    in
    case decl
      of VALdec vbs =>
	   let fun vbType(vb as VB{pat, exp, tyvars=(tv as (ref tyvars)), boundtvs}) =
	        let val (pat',pty) = patType(pat,infinity,region)
		    val (exp',ety) = expType(exp,occ,DI.next tdepth,region)
                    val generalize = TypesUtil.isValue exp
				     andalso not(TypesUtil.refutable pat)
		                     (* orelse isVarTy ety *)
		    val _ = unifyErr{ty1=pty,ty2=ety, name1="pattern", name2="expression",
			     message="pattern and expression in val dec do not agree",
			     region=region,kind=ppVB,kindname="declaration",
			     phrase=vb};
                    val vb = VB{pat=pat',exp=exp',tyvars=tv, boundtvs=
                                generalizePat(pat,tyvars,occ,tdepth,generalize,region)}
                in                              
                   debugPrint ("VB: ", ppVB, (vb,100));
                   debugmsg ("generalize: "^Bool.toString generalize);
		   vb
                end
	    in (let val _ = debugmsg ">>decType0: VALdec"
                    val d = VALdec(map vbType vbs) 
                in  
                    if (!ElabControl.oldchecker) then d
                    else (updateMonoConstraints labels; d) 
                end)
	   end

       | VALRECdec(rvbs) =>
           if (!ElabControl.oldchecker) then    
 	   let val occ = Abstr occ

	       (* First go through and type-check all the patterns and
		  result-constraints, unifying with each other and with
		  the specified result type.
	       *)
	       fun setType(rvb as RVB{var=VALvar{typ,...},exp,resultty,...}) =
                   let val domainty = mkMETAtyBounded(lamdepth occ)
		       val rangety = mkMETAtyBounded(lamdepth occ)
                                      (* depth should be infinity? *)
		       val funty = domainty --> rangety

		       val _ =
			   case resultty
			     of NONE => true
			      | SOME ty =>
				 unifyErr{ty1=funty,ty2=ty,
					  name1="",name2="constraint",
					  message="type constraint of val rec dec\
					           \ is not a function type",
					  region=region,kind=ppRVB,
					  kindname="declaration", phrase=rvb}

		       fun f(FNexp(rules,_), region, funty) =
		             let fun unify a =
				  (unifyErr{ty1=a,name1="this clause",
				    ty2=funty,name2="previous clauses",
				    message="parameter or result constraints\
			                     \ of clauses do not agree",
					   region=region,kind=ppRVB,
					   kindname="declaration", phrase=rvb};
                                  ())

				 fun approxRuleTy(RULE(pat,e)) =
				     let val (pat',pty) =
					     patType(pat,lamdepth occ,region)
				      in case e
					  of CONSTRAINTexp(e,ty) =>
					      (pat',pty-->ty,(e,region))
					   | e => (pat',pty-->rangety,(e,region))
				     end

				 val patTyExps = map approxRuleTy rules
				 val pats = map #1 patTyExps
				 val tys = map #2 patTyExps
				 val exps = map #3 patTyExps

				 fun doExp (e,region) =
				     let val (exp', ety) = expType(e,occ,tdepth,region)
				      in unifyErr{ty1=ety, name1="expression",
					  ty2=rangety, name2="result type",
					  message="right-hand-side of clause\
					\ does not agree with function result type",
					  region=region,kind=ppRVB,
					  kindname="declaration",phrase=rvb};
					 exp'
				     end

                              in app unify tys;
				 typ := funty;
				 fn()=>
				   FNexp(ListPair.map RULE (pats, map doExp exps),
						domain(prune(funty)))
			     end
		         | f(MARKexp(e,region),_,funty) =
			     let val build = f(e,region,funty)
			      in fn()=> MARKexp(build(), region)
			     end
                         | f(CONSTRAINTexp(e,ty),region,funty) =
			     let val _ =
				   unifyErr{ty1=ty, name1="this constraint",
					    ty2=funty, name2="outer constraints",
					    message="type constraints on val rec\
					             \ declaraction disagree",
					    region=region,kind=ppRVB,
					    kindname="declaration", phrase=rvb}
				 val build = f(e,region,funty)
			     in fn()=> CONSTRAINTexp(build(), ty)
			    end
			| f _ = bug "typecheck.823"
                   in f(exp,region,funty)
                  end
		 | setType _ = bug "setType"

	      (* Second, go through and type-check the right-hand-side
	         expressions (function bodies) *)

	       fun rvbType(RVB{var=v,resultty,tyvars,boundtvs,...}, build) =
                      RVB{var=v,exp=build(),
                          resultty=resultty,tyvars=tyvars,boundtvs=boundtvs}
                  
	       val _ = debugmsg ">>decType0: VALRECdec using monorec checker"
               val builders = map setType rvbs
               val rvbs' = ListPair.map rvbType (rvbs,builders)
               (* No need to generalize here, because every VALRECdec is
                  wrapped in a VALdec, and the generalization occurs at the
                  outer level.  Previously: val rvbs'' = map genType rvbs' *)
	    in 
               EU.recDecs rvbs'
	   end

           else (* polyrec checker *)
               let val _ = debugmsg ">>decType0: VALRECdec using polyrec checker"
                   val occ = Abstr occ

                   fun setType(RVB{var=VALvar{typ,...},resultty=NONE,...}) = 
                       typ := mkMETAtyBounded(1+lamdepth occ) (* was: mkRefMETAty(...) *)
                     | setType(rvb as RVB{var=VALvar{typ,...},resultty=SOME ty,...}) =
                       let 
                           val domainty = mkMETAtyBounded(lamdepth occ)
                           val rangety = mkMETAtyBounded(lamdepth occ)
                           val _ = unifyErr{ty1=domainty --> rangety,
                                            ty2=ty,
                                            name1="",name2="constraint",
                                            message="type constraint of val rec dec\
                                             \ is not a function type",
                                            region=region,kind=ppRVB,
                                            kindname="declaration", phrase=rvb}
                       in typ := ty end
                     | setType(_) = () 

                  (* Enforce user-constraints of rule-types (without unifying!) ...? *)

                   val oldrecbound = (!recbound)
                   val _ = recbound := revadd (map (fn (rvb as RVB{var=v,...}) => v) rvbs)
                                              oldrecbound
                   val thedeftys = ref([]:((ty ref * ty) list))
                       
                   fun rvbType(rvb as RVB{var=v as VALvar{typ,...},exp,
                                          resultty,tyvars,boundtvs}) =
                       let val (exp',ety) (* DI.next tdepth ? *)
                           = (expType(exp,occ,tdepth,region)) (* '93: Abstr(Rator occ) *)  
                       in 
                           (thedeftys := ((typ,ety)::(!thedeftys)));
                           RVB{var=v,exp=exp',resultty=resultty,tyvars=tyvars,boundtvs=boundtvs}
                       end
                     | rvbType _ = bug "typecheck.786"
                       
                   val doclean = if (!topprob) then (topprob:= false; true) else false

                   val _ = (app setType rvbs)
                   val rvbs' = map rvbType rvbs

                   val _ = let fun f (tref,ty) = unifyTy(!tref,ty,tyToLoc(!tref),tyToLoc ty)
                           in (app f (!thedeftys)) end
                   val _ = recbound := oldrecbound
                       
                   val _ = updateMonoConstraints labels  
                   val _ = printSolvedIneqns := 
                           (checkrvbpr1 rvbs semiprob monoConstraints)

                   val _ = semiprob := 
                        (SU.solve (!semiprob) (!monoConstraints)
                         handle SU.SFAIL(mode,inequation,L) => 
                             (printSolvedIneqns := false;  
                              err region COMPLAIN(mode) 
                              (fn ppstrm =>
                               (PPType.resetPPType();
                                PP.newline ppstrm;
                                PP.string ppstrm "problem inequation";
                                PP.newline ppstrm;
                                ppIneqlist ppstrm [inequation];
                                PP.newline ppstrm;
                                PP.string ppstrm "in current system";
                                PP.newline ppstrm;
                                ppIneqlist ppstrm (!semiprob);
                                PP.newline ppstrm;
                                PP.string ppstrm "in declaration:";
                                PP.break ppstrm {nsp=1,offset=2};
                                PPAbsyn.ppDec (env,NONE) ppstrm 
                                (VALRECdec(rvbs),!printDepth)));
                              (L)))
                   val _ = checkrvbpr2 (!printSolvedIneqns) semiprob monoConstraints

                   val _ = if doclean then (semiprob := [];
                                            monoConstraints := [];
                                            eqcounter := 0; 
                                            PPType.resetPPType();
                                            topprob := true) 
                           else ()

                   val _ = debugmsg "<<decType0: VALRECdec using polyrec checker"
               in 
                   EU.recDecs rvbs'
               end

       | DOdec exp => let
	  val (exp',ety) = expType(exp,occ,DI.next tdepth,region)
	  val _ = unifyErr{
		    ty1=unitTy, ty2=ety, name1="", name2="expression",
		    message="do expression does not have type unit",
		    region=region, kind=ppDec, kindname="declaration",
		    phrase=decl
		  }
	  in
	    DOdec exp'
	  end

       | EXCEPTIONdec(ebs) =>
	   let fun check(VARty(ref(UBOUND _))) =
		     err region COMPLAIN
		         "type variable in top level exception type"
			 nullErrorBody
		 | check(CONty(_,args)) =
		     app check args
		 | check _ = ()
	       fun ebType(EBgen{etype=SOME ty,...}) = check ty
	         | ebType _ = ()
	       val _ = debugmsg ">>decType0: EXCEPTIONdec"
            in if TypesUtil.lamdepth occ < 1 then app ebType ebs else ();
               decl
	   end
       | LOCALdec(decIn,decOut) =>
	   let
               val _ = debugmsg ">>decType0: LOCALdec decIn"
               val decIn' = decType0(decIn,LetDef occ,tdepth,region)
               val _ = debugmsg ">>decType0: LOCALdec decOut"
               val decOut' = decType0(decOut,occ,tdepth,region)
	    (*   val _ = debugmsg ">>decType0: LOCALdec" *)
            in LOCALdec(decIn',decOut')
           end
       | SEQdec(decls) =>
           SEQdec(map (fn decl => decType0(decl,occ,tdepth,region)) decls)
       | ABSTYPEdec{abstycs,withtycs,body} => 
	   let fun makeAbstract(GENtyc{eq,...}) = (eq := ABS)
		 | makeAbstract _ = bug "makeAbstract"
	       fun redefineEq(DATATYPEdec{datatycs,...}) =
		   let fun setDATA (GENtyc { eq, ... }) = eq := DATA
			 | setDATA _ = ()
		   in
		       app setDATA datatycs;
		       EqTypes.defineEqProps(datatycs,nil,EntityEnv.empty)
		   end
	         | redefineEq(SEQdec decs) = app redefineEq decs
	         | redefineEq(LOCALdec(din,dout)) =
		    (redefineEq din; redefineEq dout)
	         | redefineEq(MARKdec(dec,_)) = redefineEq dec
	         | redefineEq _ = ()
	       val body'= decType0(body,occ,tdepth,region)
	       val _ = debugmsg ">>decType0: ABSTYPEdec"
	    in app makeAbstract abstycs;
	       redefineEq body';
	       ABSTYPEdec{abstycs=abstycs,withtycs=withtycs,body=body'}
	   end
       | MARKdec(dec,region) => MARKdec(decType0(dec,occ,tdepth,region),region)

      (*
       * The next several declarations will never be seen ordinarily;
       * they are for re-typechecking after the instrumentation phase
       * of debugger or profiler.
       *)
       | STRdec strbs => STRdec(map (strbType(occ,tdepth,region)) strbs)
       | FCTdec fctbs => FCTdec(map (fctbType(occ,tdepth,region)) fctbs)
       | _ => decl
      end

and fctbType (occ,tdepth,region) (FCTB{fct,def,name}) =
      let fun fctexpType(FCTfct{param, argtycs, def}) =
  	        FCTfct{param=param, def=strexpType (occ,DI.next tdepth,region) def,
	               argtycs=argtycs}
 	    | fctexpType(LETfct(dec,e)) =
	        LETfct(decType0(dec,LetDef occ,tdepth,region), fctexpType e)
	    | fctexpType(MARKfct(f,region)) = MARKfct(fctexpType f,region)
            | fctexpType v = v
       in FCTB{fct=fct,def=fctexpType def,name=name}
      end

and strexpType (occ,tdepth,region) (se as (APPstr{oper,arg,argtycs})) = se
  | strexpType (occ,tdepth,region) (LETstr(dec,e)) =
      LETstr(decType0(dec,LetDef occ,tdepth,region), strexpType (occ,tdepth,region) e)
  | strexpType (occ,tdepth,_) (MARKstr(e,region)) =
      MARKstr(strexpType (occ,tdepth,region) e, region)
  | strexpType _ v = v

and strbType (occ,tdepth,region) (STRB{str,def,name}) =
    STRB{str=str,def=strexpType (occ,tdepth,region) def,name=name}
(*
val _ = debugmsg ">>decType: resetOverloaded"
val _ = resetOverloaded()
val _ = debugmsg ">>decType: OverloadedLit.reset"
val _ = OLL.reset ()
*)
val _ = debugmsg ">>decType: calling decType0"
val dec' = decType0(dec, if toplev then Root else (LetDef Root), tdepth, region);
val _ = ppDecDebug("<<decType0 returning with: ", dec')
in
(*
val _ = debugmsg ">>decType: OverloadedLit.resolve"
val _ = OLL.resolve ()
val _ = debugmsg ">>decType: resolveOverloaded"
val _ = resolveOverloaded env
     oll_resolve ();  -- literal overloading resolution merged with operator resolution *)
    ol_resolve env;
    checkFlex ();
    debugmsg "<<decType: returning";
    dec'
end (* function decType *)

val decType = Stats.doPhase (Stats.makePhase "Compiler 035 decType") decType

end (* local *)
end (* structure Typecheck *)

(*
 * $Log: typecheck.sml,v $
 * Revision 1.13  1997/11/11 05:29:50  dbm
 *   Fix error message (eliminate spurious newline).
 *
 * Revision 1.12  1997/11/07  05:43:48  dbm
 *   Improved wording or layout of some error messages.  Conditioned
 *   warning message regarding top-level value restriction violation
 *   on the flag Control.valueRestrictionTopWarn.
 *
 * Revision 1.11  1997/11/04  23:33:11  dbm
 *   Changed treatment of top level declarations that fail the value
 *   restriction.  Ungeneralized type variables are now instantiated
 *   to specially generated dummy types named X1, X2, etc.
 *
 * Revision 1.10  1997/10/08  21:12:28  dbm
 *   Fix for bug 1286 (Zhong).  The generalization procedure was complaining
 *   about the flex tyvars even if the depth of the tyvar was smaller than
 *   the current depth.
 *
 * Revision 1.9  1997/07/15  16:24:58  dbm
 *   Use new Control.valueRestrictionWarn flag to suppress local value
 *   restriction warnings.
 *
 * Revision 1.8  1997/04/16  22:26:35  dbm
 *   Fix for bug 317.  Recalculate equality props for datatypes in the
 *   body of an abstype after the type checker makes the abstract types
 *   abstract.
 *
 * Revision 1.7  1997/04/10  14:41:16  dbm
 *   Eliminated extra space from generalization error message.  Added local
 *   bind function and comment to generalizeTy.
 *
 * Revision 1.6  1997/04/02  04:22:36  dbm
 *   Fixed bug in 109.26 that improperly rejected some local declarations
 *    that failed the value restriction.
 *   Changed the treatment of FUNdecs to give priority to defining occurences
 *    of the defined function symbols over the applied occurences (which can
 *    sometimes occur before the defining occurences, causing confusing
 *    type error messages.
 *   Unified much of the type error message code via a function unifyErr.
 *
 * Revision 1.5  1997/03/27  17:19:16  dbm
 *   Changed test for top-level ungeneralized type variables to fix bug 1177.
 *
 * Revision 1.4  1997/03/22  18:28:01  dbm
 * Revised generalizeTy to fix bug 905/952.  Also changed the names of
 * the functions called for literal overloading.
 *
 * Revision 1.3  1997/03/18  16:46:19  dbm
 * Added test in META case of generalizeTy:gen to fix bugs 1066 and 274 (revised).
 *
 * Revision 1.2  1997/02/26  21:55:49  george
 *    Fix the bug, BUG 1139, on "unexpected type variables in mkPE" reported
 *    by Nikolaj (a.k.a. BUG 4 in his list of four bugs for 109.25)
 *
 *)

(* Modification over [Poly Rec] version 1.5 for SML/NJ Version 0.93:

 - replaced prune x = prune y by equalType(x,y) 
 - replaced compress by Semiunfiy.compressTy

 - replaced std_in by TextIO.stdIn
 - replaced input_line by TextIO.inputLine
 - replaced std_out by TextIO.stdOut
 - replaced flush_out by TextIO.flushOut

 - redefined polybound using eqVar, since Var is not an equality type

*)


