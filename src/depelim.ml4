(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

(* $Id: equations.ml4 11996 2009-03-20 01:22:58Z letouzey $ *)

open Cases
open Util
open Names
open Nameops
open Term
open Termops
open Declarations
open Inductiveops
open Environ
open Sign
open Reductionops
open Typeops
open Type_errors
open Pp
open Proof_type

open Glob_term
open Retyping
open Pretype_errors
open Evarutil
open Evarconv
open List
open Libnames
open Topconstr
open Tacmach
open Namegen
open Tacticals
open Tactics
open Evd

open Equations_common
open Sigma

let lift_togethern n l =
  let l', _ =
    List.fold_right
      (fun x (acc, n) ->
	(lift n x :: acc, succ n))
      l ([], n)
  in l'

let lift_together l = lift_togethern 0 l

let lift_list l = List.map (lift 1) l

let ids_of_constr ?(all=false) vars c =
  let rec aux vars c =
    match kind_of_term c with
    | Var id -> Idset.add id vars
    | App (f, args) -> 
	(match kind_of_term f with
	| Construct (ind,_)
	| Ind ind ->
            let (mib,mip) = Global.lookup_inductive ind in
	      array_fold_left_from
		(if all then 0 else mib.Declarations.mind_nparams)
		aux vars args
	| _ -> fold_constr aux vars c)
    | _ -> fold_constr aux vars c
  in aux vars c
    
let decompose_indapp f args =
  match kind_of_term f with
  | Construct (ind,_) 
  | Ind ind ->
      let (mib,mip) = Global.lookup_inductive ind in
      let first = mib.Declarations.mind_nparams_rec in
      let pars, args = array_chop first args in
	mkApp (f, pars), args
  | _ -> f, args

open Coqlib

let mk_term_eq env sigma ty t ty' t' =
  if Reductionops.is_conv env sigma ty ty' then
    mkEq ty t t', mkRefl ty' t'
  else
    mkHEq ty t ty' t', mkHRefl ty' t'

let make_abstract_generalize gl id concl dep ctx body c eqs args refls =
  let meta = Evarutil.new_meta() in
  let eqslen = List.length eqs in
  let term, typ = mkVar id, pf_get_hyp_typ gl id in
    (* Abstract by the "generalized" hypothesis equality proof if necessary. *)
  let abshypeq, abshypt =
    if dep then
      let eq, refl = mk_term_eq (push_rel_context ctx (pf_env gl)) (project gl) (lift 1 c) (mkRel 1) typ term in
	mkProd (Anonymous, eq, lift 1 concl), [| refl |]
    else concl, [||]
  in
    (* Abstract by equalitites *)
  let eqs = lift_togethern 1 eqs in (* lift together and past genarg *)
  let abseqs = it_mkProd_or_LetIn (lift eqslen abshypeq) (List.map (fun x -> (Anonymous, None, x)) eqs) in
    (* Abstract by the "generalized" hypothesis. *)
  let genarg = mkProd_or_LetIn (Name id, body, c) abseqs in
    (* Abstract by the extension of the context *)
  let genctyp = it_mkProd_or_LetIn genarg ctx in
    (* The goal will become this product. *)
  let genc = mkCast (mkMeta meta, DEFAULTcast, genctyp) in
    (* Apply the old arguments giving the proper instantiation of the hyp *)
  let instc = mkApp (genc, Array.of_list args) in
    (* Then apply to the original instanciated hyp. *)
  let instc = Option.cata (fun _ -> instc) (mkApp (instc, [| mkVar id |])) body in
    (* Apply the reflexivity proofs on the indices. *)
  let appeqs = mkApp (instc, Array.of_list refls) in
    (* Finaly, apply the reflexivity proof for the original hyp, to get a term of type gl again. *)
    mkApp (appeqs, abshypt)
      
let deps_of_var id env =
  Environ.fold_named_context
    (fun _ (n,b,t) (acc : Idset.t) -> 
      if Option.cata (occur_var env id) false b || occur_var env id t then
	Idset.add n acc
      else acc)
    env ~init:Idset.empty
    
let idset_of_list =
  List.fold_left (fun s x -> Idset.add x s) Idset.empty

let hyps_of_vars env sign nogen hyps =
  if Idset.is_empty hyps then [] 
  else
    let (_,lh) =
      Sign.fold_named_context_reverse
        (fun (hs,hl) (x,_,_ as d) ->
	  if Idset.mem x nogen then (hs,hl)
	  else if Idset.mem x hs then (hs,x::hl)
	  else
	    let xvars = global_vars_set_of_decl env d in
	      if not (Idset.equal (Idset.diff xvars hs) Idset.empty) then
		(Idset.add x hs, x :: hl)
	      else (hs, hl))
        ~init:(hyps,[])
        sign 
    in lh

exception Seen

let linear vars args = 
  let seen = ref vars in
    try 
      Array.iter (fun i -> 
	let rels = ids_of_constr ~all:true Idset.empty i in
	let seen' = 
	  Idset.fold (fun id acc ->
	    if Idset.mem id acc then raise Seen
	    else Idset.add id acc)
	    rels !seen
	in seen := seen')
	args;
      true
    with Seen -> false

let needs_generalization gl id =
  let f, args, def, id, oldid = 
    let oldid = pf_get_new_id id gl in
    let (_, b, t) = pf_get_hyp gl id in
      match b with
      | None -> let f, args = decompose_app t in
		  f, args, false, id, oldid
      | Some t -> 
	  let f, args = decompose_app t in
	    f, args, true, id, oldid
  in
    if args = [] then false
    else
      let args = Array.of_list args in
      let f', args' = decompose_indapp f args in
      let parvars = ids_of_constr ~all:true Idset.empty f' in
	if not (linear parvars args') then true
	else array_exists (fun x -> not (isVar x)) args'
	  
TACTIC EXTEND needs_generalization
| [ "needs_generalization" hyp(id) ] -> 
    [ fun gl -> 
      if needs_generalization gl id 
      then tclIDTAC gl
      else tclFAIL 0 (str"No generalization needed") gl ]
END
	
let abstract_args gl generalize_vars dep id defined f args =
  let sigma = project gl in
  let env = pf_env gl in
  let concl = pf_concl gl in
  let dep = dep || dependent (mkVar id) concl in
  let avoid = ref [] in
  let get_id name =
    let id = fresh_id !avoid (match name with Name n -> n | Anonymous -> id_of_string "gen_x") gl in
      avoid := id :: !avoid; id
  in
    (* Build application generalized w.r.t. the argument plus the necessary eqs.
       From env |- c : forall G, T and args : G we build
       (T[G'], G' : ctx, env ; G' |- args' : G, eqs := G'_i = G_i, refls : G' = G, vars to generalize)
       
       eqs are not lifted w.r.t. each other yet. (* will be needed when going to dependent indexes *)
    *)
  let aux (prod, ctx, ctxenv, c, args, eqs, refls, nongenvars, vars, env) arg =
    let (name, _, ty), arity =
      let rel, c = Reductionops.splay_prod_n env sigma 1 prod in
	List.hd rel, c
    in
    let argty = pf_type_of gl arg in
    let argty = refresh_universes_strict argty in 
    let lenctx = List.length ctx in
    let liftargty = lift lenctx argty in
    let leq = constr_cmp Reduction.CUMUL liftargty ty in
      match kind_of_term arg with
      | Var id when leq && not (Idset.mem id nongenvars) ->
      	  (subst1 arg arity, ctx, ctxenv, mkApp (c, [|arg|]), args, eqs, refls,
      	  Idset.add id nongenvars, Idset.remove id vars, env)
      | _ ->
	  let name = get_id name in
	  let decl = (Name name, None, ty) in
	  let ctx = decl :: ctx in
	  let c' = mkApp (lift 1 c, [|mkRel 1|]) in
	  let args = arg :: args in
	  let liftarg = lift (List.length ctx) arg in
	  let eq, refl =
	    if leq then
	      mkEq (lift 1 ty) (mkRel 1) liftarg, mkRefl (lift (-lenctx) ty) arg
	    else
	      mkHEq (lift 1 ty) (mkRel 1) liftargty liftarg, mkHRefl argty arg
	  in
	  let eqs = eq :: lift_list eqs in
	  let refls = refl :: refls in
	  let argvars = ids_of_constr vars arg in
	    (arity, ctx, push_rel decl ctxenv, c', args, eqs, refls, 
	    nongenvars, Idset.union argvars vars, env)
  in 
  let f', args' = decompose_indapp f args in
  let dogen, f', args' =
    let parvars = ids_of_constr ~all:true Idset.empty f' in
      if not (linear parvars args') then true, f, args
      else
	match array_find_i (fun i x -> not (isVar x)) args' with
	| None -> false, f', args'
	| Some nonvar ->
	    let before, after = array_chop nonvar args' in
	      true, mkApp (f', before), after
  in
    if dogen then
      let arity, ctx, ctxenv, c', args, eqs, refls, nogen, vars, env = 
	Array.fold_left aux (pf_type_of gl f',[],env,f',[],[],[],Idset.empty,Idset.empty,env) args'
      in
      let args, refls = List.rev args, List.rev refls in
      let vars = 
	if generalize_vars then
	  let nogen = Idset.add id nogen in
	    hyps_of_vars (pf_env gl) (pf_hyps gl) nogen vars
	else []
      in
      let body, c' = if defined then Some c', Retyping.get_type_of ctxenv Evd.empty c' else None, c' in
	Some (make_abstract_generalize gl id concl dep ctx body c' eqs args refls,
	     dep, succ (List.length ctx), vars)
    else None
      
let abstract_generalize ?(generalize_vars=true) ?(force_dep=false) id gl =
  Coqlib.check_required_library ["Coq";"Logic";"JMeq"];
  let f, args, def, id, oldid = 
    let oldid = pf_get_new_id id gl in
    let (_, b, t) = pf_get_hyp gl id in
      match b with
      | None -> let f, args = decompose_app t in
		  f, args, false, id, oldid
      | Some t -> 
	  let f, args = decompose_app t in
	    f, args, true, id, oldid
  in
  if args = [] then tclIDTAC gl
  else 
    let args = Array.of_list args in
    let newc = abstract_args gl generalize_vars force_dep id def f args in
      match newc with
      | None -> tclIDTAC gl
      | Some (newc, dep, n, vars) -> 
	  let tac =
	    if dep then
	      tclTHENLIST [refine newc; rename_hyp [(id, oldid)]; tclDO n intro; 
			   generalize_dep ~with_let:true (mkVar oldid)]	      
	    else
	      tclTHENLIST [refine newc; clear [id]; tclDO n intro]
	  in 
	    if vars = [] then tac gl
	    else tclTHEN tac 
	      (fun gl -> tclFIRST [revert vars ;
				   tclMAP (fun id -> 
				     tclTRY (generalize_dep ~with_let:true (mkVar id))) vars] gl) gl

(* TACTIC EXTEND dependent_generalize *)
(* | ["dependent" "generalize" hyp(id) "as" ident(id') ] ->  *)
(*     [ fun gl -> generalize_sigma (pf_env gl) (project gl) (mkVar id) id' gl ] *)
(* END *)
(* TACTIC EXTEND dep_generalize_force *)
(* | ["dependent" "generalize" "force" hyp(id) ] ->  *)
(*     [ abstract_generalize ~generalize_vars:false ~force_dep:true id ] *)
(* END *)
(* TACTIC EXTEND dependent_generalize_eqs_vars *)
(* | ["dependent" "generalize" "vars" hyp(id) ] ->  *)
(*     [ abstract_generalize ~generalize_vars:true id ] *)
(* END *)
(* TACTIC EXTEND dependent_generalize_eqs_vars_force *)
(* | ["dependent" "generalize" "force" "vars" hyp(id) ] ->  *)
(*     [ abstract_generalize ~force_dep:true ~generalize_vars:true id ] *)
(* END *)

let dependent_pattern ?(pattern_term=true) c gl =
  let cty = pf_type_of gl c in
  let deps =
    match kind_of_term cty with
    | App (f, args) -> 
	let f', args' = decompose_indapp f args in 
	  Array.to_list args'
    | _ -> []
  in
  let varname c = match kind_of_term c with
    | Var id -> id
    | _ -> pf_get_new_id (id_of_string (hdchar (pf_env gl) c)) gl
  in
  let mklambda ty (c, id, cty) =
    let conclvar = subst_closed_term_occ all_occurrences c ty in
      mkNamedLambda id cty conclvar
  in
  let subst = 
    let deps = List.rev_map (fun c -> (c, varname c, pf_type_of gl c)) deps in
      if pattern_term then (c, varname c, cty) :: deps
      else deps
  in
  let concllda = List.fold_left mklambda (pf_concl gl) subst in
  let conclapp = applistc concllda (List.rev_map pi1 subst) in
    convert_concl_no_check conclapp DEFAULTcast gl

TACTIC EXTEND dependent_pattern
| ["dependent" "pattern" constr(c) ] -> [ dependent_pattern c ]
END

TACTIC EXTEND dependent_pattern_from
| ["dependent" "pattern" "from" constr(c) ] ->
    [ dependent_pattern ~pattern_term:false c ]
END

(** wjzz start **)

(********************************************************************)
(* Analysis of the term structure *)

open Printf

let concat_string_array : string array -> string =
  fun arr ->
    let l = Array.to_list arr in
    List.fold_left (fun x y -> if x="" then y else x ^ " " ^ y) "" l

let simplify_ind_name : string -> string = 
  fun s ->
    Str.split (Str.regexp_string ".") s 
    |> List.rev
    |> List.hd

let rec str_of_c : (constr, types) kind_of_term -> string = function
  | Rel n -> string_of_int n
  | Var n -> string_of_id n
  | Meta _mv -> "meta"
  | Evar _ -> "evar"
  | Sort s ->
    begin match family_of_sort s with
      | InProp -> "Prop"
      | InSet -> "Set"
      | InType -> "Type"
    end
  | Cast _ -> "cast"
  | Prod (n, tp1, tp2) ->
    let stp1 = str_of_c (kind_of_term tp1) in
    let stp2 = str_of_c (kind_of_term tp2) in
    begin match n with
      | Anonymous ->
        sprintf "(%s -> %s)" stp1 stp2
      | Name id ->
        sprintf "(%s : %s) -> %s" 
	  (string_of_id id) stp1 stp2
    end
  | Lambda _ -> "lambda"
  | LetIn _ -> "let in"
  | App (x, xs) ->
    let sx = str_of_c (kind_of_term x) in
    let sxs = Array.map (fun c -> "(" ^ str_of_c (kind_of_term c) ^ ")") xs in
    sprintf "%s %s" sx (concat_string_array sxs)
  (* | Const cn -> sprintf "[const %s]" (string_of_con cn) *)
  | Const cn -> simplify_ind_name (string_of_con cn)
  (* | Ind (mind, _n) -> sprintf "[ind %s]" (string_of_mind mind) *)
  | Ind (mind, _n) -> simplify_ind_name (string_of_mind mind)
  | Construct _ -> "constructor"
  | Case _ -> "case"
  | Fix _ -> "fix"
  | CoFix _ -> "cofix"

let print_constr_structure : constr -> unit = 
  fun c ->
    Printf.eprintf "%s\n%!" (str_of_c (kind_of_term c))

(***************************************************************)
(* Introductions *)

(* We are only interested in equalities ... *)

(* `@eq tp lhs rhs` as record *)
type equality_info =
    { tp  : types
    ; lhs : constr
    ; rhs : constr
    }

(* `@existsT A P n x` as record *)

type constr_category =
  | Equality of Names.name * equality_info * types
  | Block
  | Product
  | Unknown

let name_of_eq : string =
  "Coq.Init.Logic.eq"

let name_of_block : string =
  "Equations.DepElim.block"

let name_of_sigT : string =
  "Coq.Init.Specif.sigT"

(* term categorization *)

let is_variable : constr -> identifier option =
  fun c ->
    match kind_of_term c with
      | Var id ->
        Some id
      | _ ->
        None

let is_ind_equality : constr -> bool =
  fun c ->
    match kind_of_term c with
      | Ind (mind, _n) when name_of_eq = string_of_mind mind ->
        true
      | _ ->
        false

let is_equality_opt : constr -> equality_info option =
  fun c ->
    match kind_of_term c with
      | App (x, xs) when is_ind_equality x && Array.length xs = 3 ->
        Some { tp = xs.(0) ; lhs = xs.(1) ; rhs = xs.(2) }
      | _ ->
        None

let is_blocked_goal : constr -> bool =
  fun c ->
    match kind_of_term c with
      | Const cn when name_of_block = string_of_con cn ->
        true
      | _ ->
        false

let test_constr : (constr, types) kind_of_term -> constr_category = function
  | Prod (n, tp1, tp2) ->
    begin match is_equality_opt tp1 with
      | Some eq_info ->
        Equality(n, eq_info, tp2)
      | None ->
        Product
    end
  | App (x, xs) when is_blocked_goal x ->
    Block
  | _ ->
    Unknown

(* fresh name generation *)

module Fresh : sig
  val gen_identifier : unit -> identifier
end = 
struct
  let fresh_id = ref 1
  let fresh_base = "HW"

  let gen_identifier () =
    let n = !fresh_id in
    let () = incr fresh_id in
    id_of_string (fresh_base ^ string_of_int n)
end

(* references to existing tactics *)

let build_unary_tactic : string -> (identifier -> tactic) =
  fun tac_name id ->
    tac_of_string tac_name
      [IntroPattern (dummy_loc, Genarg.IntroIdentifier id)]

let noconf_ref : identifier -> tactic =
  build_unary_tactic "noconf_ref" 

let revert_blocking_until : identifier -> tactic =
  build_unary_tactic "revert_blocking_until" 

(* Fully? qualified constant builder *)
(* E.g. build_constant ["A","B","C"] "lemma" gives a constant
   eqv. to "A.B.C.lemma".

   Note: it might not always work, as we set dir_path to empty.
*)

let build_constant : string list -> string -> constant =
  fun module_names lemma_name ->
    let lemma_label = Names.mk_label lemma_name in
    let dir_path = Names.empty_dirpath in
    let inner_dir_path = List.rev_map Names.id_of_string module_names in 
    let module_path = Names.MPfile (Names.make_dirpath inner_dir_path) in
    Names.make_con module_path dir_path lemma_label

(* A wrapper to help analyze what is going on when something fails *)

let rec explain_exception : exn -> unit =
  fun e -> 
    match e with
      | Refiner.FailError (l, s) as e -> 
	let s = (string_of_ppcmds (Lazy.force s)) in
	eprintf "lvl = %d; s = %s\n%!" l s
      | Compat.Loc.Exc_located (a, e2) as e ->
	(* let x = a + 1 in  *)
	let s1 = Printexc.to_string e in 
	let s2 = Printexc.to_string e2 in 
      	let () = eprintf "Raised a located exception! %s\n%s\n%!" s1 s2 in
	explain_exception e2
      | TypeError (env, err) as e->
	ppnl (Himsg.explain_type_error env Evd.empty err)
      | Logic.RefinerError referr as e-> 
	let s = Printexc.to_string e in 
	let () = eprintf "Raised an exception!\n%s\n%!" s in
	ppnl (Himsg.explain_refiner_error referr)
      | Pretype_errors.PretypeError (evd, env, err) as e ->
	let s = Printexc.to_string e in 
	let () = eprintf "Raised a type exception!\n%s\n%!" s in
	ppnl (Himsg.explain_pretype_error evd env err)	  
      | e -> 
	let s = Printexc.to_string e in 
	eprintf "Raised a generic exception!\n%s\n%!" s

let analyze_exceptions : 'a Lazy.t -> 'a =
  fun a ->
    try
      Lazy.force a
    with
      | e -> explain_exception e; raise e

(*******************************************************)
(*          the `simplify_one_dep_elim` tactic         *)
(*******************************************************)

(** coerces a lemma name into a reference **)

let create_reference_to_lemma : string -> reference =
  fun lemma ->
    let qualid = Libnames.qualid_of_ident (id_of_string lemma) in
    Qualid (dummy_loc, qualid)

(** given f and n builds (@f _ _ ... _) [n - number of holes ] **)

let build_explicit_app_with_holes : reference -> int -> constr_expr =
  fun fn hole_num ->
    let hole = Topconstr.CHole (dummy_loc, None) in
    let args = Util.list_make hole_num hole in
    Topconstr.CAppExpl (dummy_loc, (None, fn), args)

(** given lemma name, dummy argument number, and the final type
    creates the term argument for refine **)

let build_refine_argument_in_steps : string -> int -> goal sigma -> open_constr =
  fun fn_name hole_num gl ->
    let ref_name = create_reference_to_lemma fn_name in
    let cexpr = build_explicit_app_with_holes ref_name hole_num in
    let goal_type = pf_concl gl in

    let glob_expr = 
      Constrintern.intern_gen false Evd.empty Environ.empty_env
	~allow_patvar:false ~ltacvars:([], []) cexpr in
    let oconstr : open_constr = Tacinterp.interp_open_constr_wjzz gl glob_expr in
    oconstr

let call_refine : tactic = 
  fun gl ->
    analyze_exceptions (lazy
    (* let () = ppnl (Printer.pr_goal gl) in  *)
    let open_constr = build_refine_argument_in_steps "solution_left" 4 gl in
    (* let () = Printf.printf "calling refine...\n" in *)
    Refine.refine open_constr gl
    )

let wjzz_eq_case : Names.name -> equality_info -> types -> identifier -> tactic =
  fun n eqinfo tp2 id ->
    match is_variable eqinfo.lhs , is_variable eqinfo.rhs with
      | Some x , _ ->
        tclTHENLIST
          [ Hiddentac.h_move true id (MoveBefore x)
	  ; Hiddentac.h_move true x  (MoveBefore id)
          ; revert_blocking_until x
          ; Hiddentac.h_revert [ x ]
	  ; call_refine
	  ; tclIDTAC_MESSAGE (str "Refine successful!\n")
          ]
      | None, Some y ->
	(* TODO? *)
        Tacmach.refine (mkVar (id_of_string "solution_right"))
      | None , None ->
	let () = eprintf "l = %s\nr = %s\n%!"
	  (str_of_c (kind_of_term eqinfo.lhs))
	  (str_of_c (kind_of_term eqinfo.rhs)) in
        tclIDTAC

let wjzz_print_arg : (constr, types) kind_of_term -> unit = 
  fun ck -> 
    let () = eprintf "%s\n%!" (str_of_c ck) in
    let () = match test_constr ck with
      | Equality (n, eqinfo, tp2) ->
	eprintf "l = %s\nr = %s\n%!"
	  (str_of_c (kind_of_term eqinfo.lhs))
	  (str_of_c (kind_of_term eqinfo.rhs)) 
      | _ -> 
	()
    in
    ()

let simplify_one : constr -> tactic = 
  fun c ->
    let id = Fresh.gen_identifier () in
    let ck = kind_of_term c in
    (* let () = wjzz_print_arg ck in *)
    match test_constr ck with
      | Equality (n, eq, tp2) ->
        let id = Fresh.gen_identifier () in
        tclTHEN (Hiddentac.h_intro id)
          (wjzz_eq_case n eq tp2 id)

      | Block ->
        tclFAIL 0 (str "Block reached!")

      | Product | Unknown ->
	Hiddentac.h_intro_move None (MoveToEnd true)

TACTIC EXTEND wjzz_test
[ "wjzz_simplify_one_dep_elim" constr(c) ] -> [ simplify_one c ]
END

(*
(Coq.Init.Logic.eq Coq.Init.Specif.sigT A lambda constructor A lambda x0 x constructor A lambda x1 y -> Coq.Init.Logic.False)
l = constructor A lambda x0 x
r = constructor A lambda x1 y
HELLO2
*)
(*
(Coq.Init.Logic.eq Coq.Init.Specif.sigT A lambda constructor A lambda x1 x constructor A lambda x1 y -> Coq.Init.Logic.False)
l = constructor A lambda x1 x
r = constructor A lambda x1 y
HELLO
*)
(* simplification_existT1 simplification_existT2 simplification_existT2_dec *)
