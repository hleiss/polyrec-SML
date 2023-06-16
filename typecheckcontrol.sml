(* File polyrec-SML/typecheckcontrol.sml            H.Leiss June 2023
 *
 * Control flags used by semiunify.sml and typecheck.polyrec.sml
 * (extracted from a 1998 modification of CG_Control of smlnj-110.0.3
 *  to be included in Elab(Control):ELABCONTROL of smlnj-110.99.3)
 *)

(* typechecker controls, to be included in ELABCONTROL *)

signature TYPECHECK_CONTROL =
  sig
    val oldchecker : bool ref 
    val viewsemi : int ref 
    val showsemi : {Var : int ref, 
                    Rule : int ref, 
                    Let : int ref, 
                    Valrec : int ref, 
                    Step : int ref}
  end
   
(* Type checker controls / debug flags, used in typecheck and semiunify *)

structure TypecheckControl : TYPECHECK_CONTROL =
  struct
    val oldchecker = ref true    (* use Control.usepoly() for polyrec checker *)
    val viewsemi = ref 1         (* show type checking of Var,...,Valrec case *)
    val showsemi = {Var = ref 3, (*   if !viewsemi > (!(# Var showsemi) etc.  *)
                    Rule = ref 5,
                    Let = ref 4, 
                    Valrec = ref 1,
                    Step = ref 2}

  end
  
