signature FINDDECVARS = sig
    val find_dec_vars : Absyn.dec -> Semiunify.ineqlabel list
    val find_var_var : VarCon.var -> Semiunify.ineqlabel
end 

structure Findvars (* : FINDDECVARS *) = 
struct
open Semiunify Array List Types VarCon Access BasicTypes TypesUtil Unify Absyn 

fun flatten [] = [] | flatten (x::y) = x @ (flatten y)

exception findVar

fun find_var_var(var) = 
    case var 
	of VALvar({access=access,path=path,...}) => mylab(access,SymPath.last(path))
      | OVLDvar({name,...}) => mylab(NO_ACCESS,name)  
                 (* NO_ACCESS only because the access-attrib of '93 vanished *)
      | _ => raise findVar


and find_pat_vars(pat) =
    case pat 
        of VARpat(var) => [find_var_var(var)]
      | RECORDpat({fields=labpatlist,...}) =>
	    flatten(map (fn (x,p) => find_pat_vars(p)) labpatlist) 
      | APPpat(_,_,p) => find_pat_vars(p)
      | CONSTRAINTpat(p,_) => find_pat_vars(p)
      | LAYEREDpat(p1,p2) => (find_pat_vars(p1)@find_pat_vars(p2))
      | ORpat(p1,p2) => (find_pat_vars(p1)@find_pat_vars(p2))
      | _ => []

and find_dec_vars(dec) =
    case dec
	of VALdec(vblist) => 
	    let fun find_vb_vars (VB{pat = pat,...}) = find_pat_vars(pat)
	    in (flatten(map find_vb_vars vblist))
	    end
      | VALRECdec(rvblist) => 
	    let fun find_rvb_vars (RVB{var = var,...}) = find_var_var(var)
	    in (map find_rvb_vars rvblist)
	    end
      | LOCALdec(dec1,dec2) => (find_dec_vars(dec1)@find_dec_vars(dec2))
      | SEQdec(declist) => flatten(map find_dec_vars declist)
      | MARKdec(d,region) => find_dec_vars(d)
      | _ => []


end
