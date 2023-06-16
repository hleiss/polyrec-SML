(* version.sml generated from version.template, 
 *
 * modified by adding [Poly Rec] to the system name by H.Leiss, June 2023
 *
 * COPYRIGHT (c) 2019 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
 *
 * Author: Matthias Blume (blume@tti-c.org)
 *)

structure SMLNJVersion : sig

    val version : {
            system : string,      	(* the system title *)
	    version_id : int list,	(* the version number *)
            date : string         	(* date of creation *)
	  }

    val banner : string

  end = struct

    val size = Int.toString(SMLofNJ.SysInfo.getArchSize())

    (* generate date string at boot time *)
    val version = {
	    system = "SML of New Jersey [Poly Rec]",
	    version_id = [110, 99, 3],
	    date = Date.toString (Date.fromTimeLocal (Time.now ()))
        }

    val banner = concat [
	    #system version, " (", size, "-bit)",
	    " v", String.concatWithMap "." Int.toString (#version_id version),
	    " [built: ", #date version, "]"
	  ]

  end
