(* Copyright 1991 by AT&T Bell Laboratories *)
(* Modified for Poly Rec by H.Leiss, cis.uni-muenchen.de *)

signature PPTYPELIST =
    sig	
	type ineq
	val ppineqlist : StaticEnv.staticEnv -> PrettyPrint.stream -> ineq list -> unit
	val pptypelist : StaticEnv.staticEnv -> PrettyPrint.stream -> Types.ty list -> unit
    end 

structure PPTypelist :PPTYPELIST =
struct

local open ErrorMsg Types List PPUtil 
in 
    structure PP = PrettyPrint

    type ineq = Semiunify.ineq
    val pps = PP.string

    val debugging = ref false ; (* Control.debugging (* bool ref *) *)

    fun ppType env ppstrm ty = 
        if !debugging then
            ElabDebug.withInternals (fn () => PPType.ppType env ppstrm ty)
        else PPType.ppType env ppstrm ty

    fun ppineqlist1 env ppstrm L =
         let val pps = PP.string ppstrm
         in
            app (fn (Semiunify.ineq(Semiunify.mylab(_,lab),i,ty1,ty2)) =>
                 (PP.openHVBox ppstrm (PP.Rel 0);
                  pps "(";
                  ppType env ppstrm ty1;
                  pps "  <"; pps (Int.toString i); pps " ";
                  pps (Symbol.name lab); pps "  "; 
                  ppType env ppstrm ty2; 
                  pps ")";
                  PP.newline ppstrm;
                  PP.closeBox ppstrm)) L
         end
         
    and pptypelist1 env ppstrm (ty::rest) =
            (ppType env ppstrm ty;
             PP.string ppstrm ",  ";
             pptypelist1 env ppstrm rest)
      | pptypelist1 env ppstrm [] = ()

    and ppineqlist (env:StaticEnv.staticEnv) ppstrm (ineqs:ineq list) : unit = 
        (PP.openHOVBox ppstrm (PP.Rel 1);
         ppineqlist1 env ppstrm ineqs;
         PP.closeBox ppstrm)

    and pptypelist (env:StaticEnv.staticEnv) ppstrm (tylist:ty list) : unit = 
        (PP.openHOVBox ppstrm (PP.Rel 1);
         pptypelist1 env ppstrm tylist;
         PP.closeBox ppstrm)

    val g = PrettyPrint.with_pp(ErrorMsg.defaultConsumer())


end
end (* structure PPTypelist *)





