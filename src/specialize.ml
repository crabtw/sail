(**************************************************************************)
(*     Sail                                                               *)
(*                                                                        *)
(*  Copyright (c) 2013-2017                                               *)
(*    Kathyrn Gray                                                        *)
(*    Shaked Flur                                                         *)
(*    Stephen Kell                                                        *)
(*    Gabriel Kerneis                                                     *)
(*    Robert Norton-Wright                                                *)
(*    Christopher Pulte                                                   *)
(*    Peter Sewell                                                        *)
(*    Alasdair Armstrong                                                  *)
(*    Brian Campbell                                                      *)
(*    Thomas Bauereiss                                                    *)
(*    Anthony Fox                                                         *)
(*    Jon French                                                          *)
(*    Dominic Mulligan                                                    *)
(*    Stephen Kell                                                        *)
(*    Mark Wassell                                                        *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(**************************************************************************)

open Ast
open Ast_util
open Rewriter

let opt_ddump_spec_ast = ref None

let is_typ_ord_arg = function
  | A_aux (A_typ _, _) -> true
  | A_aux (A_order _, _) -> true
  | _ -> false

type specialization = {
    is_polymorphic : kinded_id -> bool;
    instantiation_filter : kid -> typ_arg -> bool;
    extern_filter : (string * string) list -> bool
  }

let typ_ord_specialization = {
    is_polymorphic = (fun kopt -> is_typ_kopt kopt || is_order_kopt kopt);
    instantiation_filter = (fun _ -> is_typ_ord_arg);
    extern_filter = (fun _ -> false)
  }

let int_specialization = {
    is_polymorphic = is_int_kopt;
    instantiation_filter = (fun _ arg -> match arg with A_aux (A_nexp (Nexp_aux (Nexp_constant _, _)), _) -> true | _ -> false);
    extern_filter = (fun externs -> match Ast_util.extern_assoc "c" externs with Some _ -> true | None -> false)
  }

let int_specialization_with_externs = {
    is_polymorphic = is_int_kopt;
    instantiation_filter = (fun _ arg -> match arg with A_aux (A_nexp (Nexp_aux (Nexp_constant _, _)), _) -> true | _ -> false);
    extern_filter = (fun _ -> false)
  }

let rec nexp_simp_typ (Typ_aux (typ_aux, l)) =
  let typ_aux = match typ_aux with
    | Typ_id v -> Typ_id v
    | Typ_var kid -> Typ_var kid
    | Typ_tup typs -> Typ_tup (List.map nexp_simp_typ typs)
    | Typ_app (f, args) -> Typ_app (f, List.map nexp_simp_typ_arg args)
    | Typ_exist (kids, nc, typ) -> Typ_exist (kids, nc, nexp_simp_typ typ)
    | Typ_fn (arg_typs, ret_typ, effect) ->
       Typ_fn (List.map nexp_simp_typ arg_typs, nexp_simp_typ ret_typ, effect)
    | Typ_bidir (t1, t2) -> Typ_bidir (nexp_simp_typ t1, nexp_simp_typ t2)
    | Typ_internal_unknown -> Reporting.unreachable l __POS__ "escaped Typ_internal_unknown"
  in
  Typ_aux (typ_aux, l)
and nexp_simp_typ_arg (A_aux (typ_arg_aux, l)) =
  let typ_arg_aux = match typ_arg_aux with
    | A_nexp n -> A_nexp (nexp_simp n)
    | A_typ typ -> A_typ (nexp_simp_typ typ)
    | A_order ord -> A_order ord
    | A_bool nc -> A_bool (constraint_simp nc)
  in
  A_aux (typ_arg_aux, l)

(* We have to be careful about whether the typechecker has renamed anything returned by instantiation_of.
   This part of the typechecker API is a bit ugly. *)
let fix_instantiation spec instantiation =
  let instantiation = KBindings.bindings (KBindings.filter spec.instantiation_filter instantiation) in
  let instantiation = List.map (fun (kid, arg) -> Type_check.orig_kid kid, nexp_simp_typ_arg arg) instantiation in
  List.fold_left (fun m (k, v) -> KBindings.add k v m) KBindings.empty instantiation

(* polymorphic_functions returns all functions that are polymorphic
   for some set of kinded-identifiers, specified by the is_kopt
   predicate. For example, polymorphic_functions is_int_kopt will
   return all Int-polymorphic functions. *)
let rec polymorphic_functions ctx (Defs defs) =
  match defs with
  | DEF_spec (VS_aux (VS_val_spec (TypSchm_aux (TypSchm_ts (typq, typ) , _), id, externs, _), _)) :: defs ->
     let is_polymorphic = List.exists ctx.is_polymorphic (quant_kopts typq) in
     if is_polymorphic && not (ctx.extern_filter externs) then
       IdSet.add id (polymorphic_functions ctx (Defs defs))
     else
       polymorphic_functions ctx (Defs defs)
  | _ :: defs -> polymorphic_functions ctx (Defs defs)
  | [] -> IdSet.empty

(* When we specialize a function, we need to generate new name. To do
   this we take the instantiation that the new function is specialized
   for and turn that into a string in such a way that alpha-equivalent
   instantiations always get the same name. We then zencode that
   string so it is a valid identifier name, and prepend it to the
   previous function name. *)
let string_of_instantiation instantiation =
  let open Type_check in
  let kid_names = ref KOptMap.empty in
  let kid_counter = ref 0 in
  let kid_name kid =
    try KOptMap.find kid !kid_names with
    | Not_found ->
       let n = string_of_int !kid_counter in
       kid_names := KOptMap.add kid n !kid_names;
       incr kid_counter;
       n
  in

  (* We need custom string_of functions to ensure that alpha-equivalent definitions get the same name *)
  let rec string_of_nexp = function
    | Nexp_aux (nexp, _) -> string_of_nexp_aux nexp
  and string_of_nexp_aux = function
    | Nexp_id id -> string_of_id id
    | Nexp_var kid -> kid_name (mk_kopt K_int kid)
    | Nexp_constant c -> Big_int.to_string c
    | Nexp_times (n1, n2) -> "(" ^ string_of_nexp n1 ^ " * " ^ string_of_nexp n2 ^ ")"
    | Nexp_sum (n1, n2) -> "(" ^ string_of_nexp n1 ^ " + " ^ string_of_nexp n2 ^ ")"
    | Nexp_minus (n1, n2) -> "(" ^ string_of_nexp n1 ^ " - " ^ string_of_nexp n2 ^ ")"
    | Nexp_app (id, nexps) -> string_of_id id ^ "(" ^ Util.string_of_list "," string_of_nexp nexps ^ ")"
    | Nexp_exp n -> "2 ^ " ^ string_of_nexp n
    | Nexp_neg n -> "- " ^ string_of_nexp n
  in

  let rec string_of_typ = function
    | Typ_aux (typ, l) -> string_of_typ_aux typ
  and string_of_typ_aux = function
    | Typ_id id -> string_of_id id
    | Typ_var kid -> kid_name (mk_kopt K_type kid)
    | Typ_tup typs -> "(" ^ Util.string_of_list ", " string_of_typ typs ^ ")"
    | Typ_app (id, args) -> string_of_id id ^ "(" ^ Util.string_of_list "," string_of_typ_arg args ^ ")"
    | Typ_fn (arg_typs, ret_typ, eff) ->
       "(" ^ Util.string_of_list ", " string_of_typ arg_typs ^ ") -> " ^ string_of_typ ret_typ ^ " effect " ^ string_of_effect eff
    | Typ_bidir (t1, t2) ->
       string_of_typ t1 ^ " <-> " ^ string_of_typ t2
    | Typ_exist (kids, nc, typ) ->
       "exist " ^ Util.string_of_list " " kid_name kids ^ ", " ^ string_of_n_constraint nc ^ ". " ^ string_of_typ typ
    | Typ_internal_unknown -> "UNKNOWN"
  and string_of_typ_arg = function
    | A_aux (typ_arg, l) -> string_of_typ_arg_aux typ_arg
  and string_of_typ_arg_aux = function
    | A_nexp n -> string_of_nexp n
    | A_typ typ -> string_of_typ typ
    | A_order o -> string_of_order o
    | A_bool nc -> string_of_n_constraint nc
  and string_of_n_constraint = function
    | NC_aux (NC_equal (n1, n2), _) -> string_of_nexp n1 ^ " = " ^ string_of_nexp n2
    | NC_aux (NC_not_equal (n1, n2), _) -> string_of_nexp n1 ^ " != " ^ string_of_nexp n2
    | NC_aux (NC_bounded_ge (n1, n2), _) -> string_of_nexp n1 ^ " >= " ^ string_of_nexp n2
    | NC_aux (NC_bounded_gt (n1, n2), _) -> string_of_nexp n1 ^ " > " ^ string_of_nexp n2
    | NC_aux (NC_bounded_le (n1, n2), _) -> string_of_nexp n1 ^ " <= " ^ string_of_nexp n2
    | NC_aux (NC_bounded_lt (n1, n2), _) -> string_of_nexp n1 ^ " < " ^ string_of_nexp n2
    | NC_aux (NC_or (nc1, nc2), _) ->
       "(" ^ string_of_n_constraint nc1 ^ " | " ^ string_of_n_constraint nc2 ^ ")"
    | NC_aux (NC_and (nc1, nc2), _) ->
       "(" ^ string_of_n_constraint nc1 ^ " & " ^ string_of_n_constraint nc2 ^ ")"
    | NC_aux (NC_set (kid, ns), _) ->
       kid_name (mk_kopt K_int kid) ^ " in {" ^ Util.string_of_list ", " Big_int.to_string ns ^ "}"
    | NC_aux (NC_true, _) -> "true"
    | NC_aux (NC_false, _) -> "false"
    | NC_aux (NC_var kid, _) -> kid_name (mk_kopt K_bool kid)
    | NC_aux (NC_app (id, args), _) -> string_of_id id ^ "(" ^ Util.string_of_list "," string_of_typ_arg args ^ ")"
  in

  let string_of_binding (kid, arg) = string_of_kid kid ^ "=>" ^ string_of_typ_arg arg in
  Util.zencode_string (Util.string_of_list ", " string_of_binding (KBindings.bindings instantiation))

let id_of_instantiation id instantiation =
  let str = string_of_instantiation instantiation in
  prepend_id (str ^ "#") id

let rec variant_generic_typ id (Defs defs) =
  match defs with
  | DEF_type (TD_aux (TD_variant (id', typq, _, _), _)) :: _ when Id.compare id id' = 0 ->
     mk_typ (Typ_app (id', List.map (fun kopt -> mk_typ_arg (A_typ (mk_typ (Typ_var (kopt_kid kopt))))) (quant_kopts typq)))
  | _ :: defs -> variant_generic_typ id (Defs defs)
  | [] -> failwith ("No variant with id " ^ string_of_id id)

(* Returns a list of all the instantiations of a function id in an
   ast. Also works with union constructors, and searches for them in
   patterns. *)
let rec instantiations_of spec id ast =
  let instantiations = ref [] in

  let inspect_exp = function
    | E_aux (E_app (id', _), _) as exp when Id.compare id id' = 0 ->
       let instantiation = fix_instantiation spec (Type_check.instantiation_of exp) in
       instantiations := instantiation :: !instantiations;
       exp
    | exp -> exp
  in

  (* We need to to check patterns in case id is a union constructor
     that is never called like a function. *)
  let inspect_pat = function
    | P_aux (P_app (id', _), annot) as pat when Id.compare id id' = 0 ->
       begin match Type_check.typ_of_annot annot with
       | Typ_aux (Typ_app (variant_id, _), _) as typ ->
          let open Type_check in
          let instantiation = unify (fst annot) (env_of_annot annot)
                                (tyvars_of_typ (variant_generic_typ variant_id ast))
                                (variant_generic_typ variant_id ast)
                                typ
          in
          instantiations := fix_instantiation spec instantiation :: !instantiations;
          pat
       | Typ_aux (Typ_id variant_id, _) -> pat
       | _ -> failwith ("Union constructor " ^ string_of_pat pat ^ " has non-union type")
       end
    | pat -> pat
  in

  let rewrite_pat = { id_pat_alg with p_aux = (fun (pat, annot) -> inspect_pat (P_aux (pat, annot))) } in
  let rewrite_exp = { id_exp_alg with pat_alg = rewrite_pat;
                                      e_aux = (fun (exp, annot) -> inspect_exp (E_aux (exp, annot))) } in
  let _ = rewrite_defs_base { rewriters_base with rewrite_exp = (fun _ -> fold_exp rewrite_exp);
                                                  rewrite_pat = (fun _ -> fold_pat rewrite_pat)} ast in

  !instantiations

let rec rewrite_polymorphic_calls spec id ast =
  let vs_ids = val_spec_ids ast in

  let rewrite_e_aux = function
    | E_aux (E_app (id', args), annot) as exp when Id.compare id id' = 0 ->
       let instantiation = fix_instantiation spec (Type_check.instantiation_of exp) in
       let spec_id = id_of_instantiation id instantiation in
       (* Make sure we only generate specialized calls when we've
          specialized the valspec. The valspec may not be generated if
          a polymorphic function calls another polymorphic function.
          In this case a specialization of the first may require that
          the second needs to be specialized again, but this may not
          have happened yet. *)
       if IdSet.mem spec_id vs_ids then
         E_aux (E_app (spec_id, args), annot)
       else
         exp
    | exp -> exp
  in

  let rewrite_exp = { id_exp_alg with e_aux = (fun (exp, annot) -> rewrite_e_aux (E_aux (exp, annot))) } in
  rewrite_defs_base { rewriters_base with rewrite_exp = (fun _ -> fold_exp rewrite_exp) } ast

let rec typ_frees ?exs:(exs=KidSet.empty) (Typ_aux (typ_aux, l)) =
  match typ_aux with
  | Typ_id v -> KidSet.empty
  | Typ_var kid when KidSet.mem kid exs -> KidSet.empty
  | Typ_var kid -> KidSet.singleton kid
  | Typ_tup typs -> List.fold_left KidSet.union KidSet.empty (List.map (typ_frees ~exs:exs) typs)
  | Typ_app (f, args) -> List.fold_left KidSet.union KidSet.empty (List.map (typ_arg_frees ~exs:exs) args)
  | Typ_exist (kopts, nc, typ) -> typ_frees ~exs:(KidSet.of_list (List.map kopt_kid kopts)) typ
  | Typ_fn (arg_typs, ret_typ, _) ->
     List.fold_left KidSet.union (typ_frees ~exs:exs ret_typ) (List.map (typ_frees ~exs:exs) arg_typs)
  | Typ_bidir (t1, t2) -> KidSet.union (typ_frees ~exs:exs t1) (typ_frees ~exs:exs t2)
  | Typ_internal_unknown -> Reporting.unreachable l __POS__ "escaped Typ_internal_unknown"
and typ_arg_frees ?exs:(exs=KidSet.empty) (A_aux (typ_arg_aux, l)) =
  match typ_arg_aux with
  | A_nexp n -> KidSet.empty
  | A_typ typ -> typ_frees ~exs:exs typ
  | A_order ord -> KidSet.empty
  | A_bool _ -> KidSet.empty

let rec typ_int_frees ?exs:(exs=KidSet.empty) (Typ_aux (typ_aux, l)) =
  match typ_aux with
  | Typ_id v -> KidSet.empty
  | Typ_var kid -> KidSet.empty
  | Typ_tup typs -> List.fold_left KidSet.union KidSet.empty (List.map (typ_int_frees ~exs:exs) typs)
  | Typ_app (f, args) -> List.fold_left KidSet.union KidSet.empty (List.map (typ_arg_int_frees ~exs:exs) args)
  | Typ_exist (kopts, nc, typ) -> typ_int_frees ~exs:(KidSet.of_list (List.map kopt_kid kopts)) typ
  | Typ_fn (arg_typs, ret_typ, _) ->
     List.fold_left KidSet.union (typ_int_frees ~exs:exs ret_typ) (List.map (typ_int_frees ~exs:exs) arg_typs)
  | Typ_bidir (t1, t2) -> KidSet.union (typ_int_frees ~exs:exs t1) (typ_int_frees ~exs:exs t2)
  | Typ_internal_unknown -> Reporting.unreachable l __POS__ "escaped Typ_internal_unknown"
and typ_arg_int_frees ?exs:(exs=KidSet.empty) (A_aux (typ_arg_aux, l)) =
  match typ_arg_aux with
  | A_nexp n -> KidSet.diff (tyvars_of_nexp n) exs
  | A_typ typ -> typ_int_frees ~exs:exs typ
  | A_order ord -> KidSet.empty
  | A_bool _ -> KidSet.empty

(* Implicit arguments have restrictions that won't hold
   post-specialisation, but we can just remove them and turn them into
   regular arguments. *)
let rec remove_implicit (Typ_aux (aux, l) as t) =
  match aux with
  | Typ_internal_unknown -> Typ_aux (Typ_internal_unknown, l)
  | Typ_tup typs -> Typ_aux (Typ_tup (List.map remove_implicit typs), l)
  | Typ_fn (arg_typs, ret_typ, effs) -> Typ_aux (Typ_fn (List.map remove_implicit arg_typs, remove_implicit ret_typ, effs), l)
  | Typ_bidir (typ1, typ2) -> Typ_aux (Typ_bidir (remove_implicit typ1, remove_implicit typ2), l)
  | Typ_app (Id_aux (Id "implicit", _), args) -> Typ_aux (Typ_app (mk_id "atom", List.map remove_implicit_arg args), l)
  | Typ_app (id, args) -> Typ_aux (Typ_app (id, List.map remove_implicit_arg args), l)
  | Typ_id id -> Typ_aux (Typ_id id, l)
  | Typ_exist (kopts, nc, typ) -> Typ_aux (Typ_exist (kopts, nc, remove_implicit typ), l)
  | Typ_var v -> Typ_aux (Typ_var v, l)
and remove_implicit_arg (A_aux (aux, l)) =
  match aux with
  | A_typ typ -> A_aux (A_typ (remove_implicit typ), l)
  | arg -> A_aux (arg, l)

let kopt_arg = function
  | KOpt_aux (KOpt_kind (K_aux (K_int, _), kid), _) -> arg_nexp (nvar kid)
  | KOpt_aux (KOpt_kind (K_aux (K_type,_), kid), _) -> arg_typ (mk_typ (Typ_var kid))
  | KOpt_aux (KOpt_kind (K_aux (K_bool, _), kid), _) -> arg_bool (nc_var kid)
  | KOpt_aux (KOpt_kind (K_aux (K_order, _), kid), _) -> arg_order (mk_ord (Ord_var kid))

(* For numeric type arguments we have to be careful not to run into a
   situation where we have an instantiation like

   'n => 'm, 'm => 8

   and end up re-writing 'n to 8. This function turns an instantition
   like the above into two,

   'n => 'i#m, 'm => 8 and 'i#m => 'm

   so we can do the substitution in two steps. *)
let safe_instantiation instantiation =
  let args =
    List.map (fun (_, arg) -> kopts_of_typ_arg arg) (KBindings.bindings instantiation)
    |> List.fold_left KOptSet.union KOptSet.empty
    |> KOptSet.elements
  in
  List.fold_left (fun (i, r) v -> KBindings.map (fun arg -> subst_kid typ_arg_subst (kopt_kid v) (prepend_kid "i#" (kopt_kid v)) arg) i,
                                  KBindings.add (prepend_kid "i#" (kopt_kid v)) (kopt_arg v) r)
                 (instantiation, KBindings.empty) args

let instantiate_constraints instantiation ncs =
  List.map (fun c -> List.fold_left (fun c (v, a) -> constraint_subst v a c) c (KBindings.bindings instantiation)) ncs

let specialize_id_valspec spec instantiations id ast =
  match split_defs (is_valspec id) ast with
  | None -> Reporting.unreachable (id_loc id) __POS__ ("Valspec " ^ string_of_id id ^ " does not exist!")
  | Some (pre_ast, vs, post_ast) ->
     let typschm, externs, is_cast, annot = match vs with
       | DEF_spec (VS_aux (VS_val_spec (typschm, _, externs, is_cast), annot)) -> typschm, externs, is_cast, annot
       | _ -> Reporting.unreachable (id_loc id) __POS__ "val-spec is not actually a val-spec"
     in
     let TypSchm_aux (TypSchm_ts (typq, typ), _) = typschm in

     (* Keep track of the specialized ids to avoid generating things twice. *)
     let spec_ids = ref IdSet.empty in

     let specialize_instance instantiation =
       let safe_instantiation, reverse = safe_instantiation instantiation in
       (* Replace the polymorphic type variables in the type with their concrete instantiation. *)
       let typ = remove_implicit (Type_check.subst_unifiers reverse (Type_check.subst_unifiers safe_instantiation typ)) in

       (* Collect any new type variables introduced by the instantiation *)
       let collect_kids kidsets = KidSet.elements (List.fold_left KidSet.union KidSet.empty kidsets) in
       let typ_frees = KBindings.bindings instantiation |> List.map snd |> List.map typ_arg_frees |> collect_kids in
       let int_frees = KBindings.bindings instantiation |> List.map snd |> List.map typ_arg_int_frees |> collect_kids in

       (* Remove type variables from the type quantifier. *)
       let kopts, constraints = quant_split typq in
       let constraints = instantiate_constraints safe_instantiation constraints in
       let constraints = instantiate_constraints reverse constraints in
       let kopts = List.filter (fun kopt -> not (spec.is_polymorphic kopt && KBindings.mem (kopt_kid kopt) safe_instantiation)) kopts in
       let typq =
         if List.length (typ_frees @ int_frees) = 0 && List.length kopts = 0 then
           mk_typquant []
         else
           mk_typquant (List.map (mk_qi_id K_type) typ_frees
                        @ List.map (mk_qi_id K_int) int_frees
                        @ List.map mk_qi_kopt kopts
                        @ List.map mk_qi_nc constraints) in
       let typschm = mk_typschm typq typ in

       let spec_id = id_of_instantiation id instantiation in

       if IdSet.mem spec_id !spec_ids then [] else
         begin
           spec_ids := IdSet.add spec_id !spec_ids;
           [DEF_spec (VS_aux (VS_val_spec (typschm, spec_id, externs, is_cast), annot))]
         end
     in

     let specializations = List.map specialize_instance instantiations |> List.concat in

     append_ast pre_ast (append_ast (Defs (vs :: specializations)) post_ast)

(* When we specialize a function definition we also need to specialize
   all the types that appear as annotations within the function
   body. Also remove any type-annotation from the fundef itself,
   because at this point we have that as a separate valspec.*)
let specialize_annotations instantiation fdef =
  let open Type_check in
  let rw_pat = {
      id_pat_alg with
      p_typ = (fun (typ, pat) -> P_typ (subst_unifiers instantiation typ, pat))
    } in
  let rw_exp = {
      id_exp_alg with
      e_cast = (fun (typ, exp) -> E_cast (subst_unifiers instantiation typ, exp));
      lEXP_cast = (fun (typ, lexp) -> LEXP_cast (subst_unifiers instantiation typ, lexp));
      pat_alg = rw_pat
    } in
  let fdef =
    rewrite_fun {
        rewriters_base with
        rewrite_exp = (fun _ -> fold_exp rw_exp);
        rewrite_pat = (fun _ -> fold_pat rw_pat)
      } fdef
  in
  match fdef with
  | FD_aux (FD_function (rec_opt, _, eff_opt, funcls), annot) ->
     FD_aux (FD_function (rec_opt,
                          Typ_annot_opt_aux (Typ_annot_opt_none, Parse_ast.Unknown),
                          eff_opt,
                          funcls),
             annot)

let specialize_id_fundef instantiations id ast =
  match split_defs (is_fundef id) ast with
  | None -> ast
  | Some (pre_ast, DEF_fundef fundef, post_ast) ->
     let spec_ids = ref IdSet.empty in
     let specialize_fundef instantiation =
       let spec_id = id_of_instantiation id instantiation in
       if IdSet.mem spec_id !spec_ids then [] else
         begin
           spec_ids := IdSet.add spec_id !spec_ids;
           [DEF_fundef (specialize_annotations instantiation (rename_fundef spec_id fundef))]
         end
     in
     let fundefs = List.map specialize_fundef instantiations |> List.concat in
     append_ast pre_ast (append_ast (Defs (DEF_fundef fundef :: fundefs)) post_ast)
  | Some _ -> assert false (* unreachable *)

let specialize_id_overloads instantiations id (Defs defs) =
  let ids = IdSet.of_list (List.map (id_of_instantiation id) instantiations) in

  let rec rewrite_overloads defs =
    match defs with
    | DEF_overload (overload_id, overloads) :: defs ->
       let overloads = List.concat (List.map (fun id' -> if Id.compare id' id = 0 then IdSet.elements ids else [id']) overloads) in
       DEF_overload (overload_id, overloads) :: rewrite_overloads defs
    | def :: defs -> def :: rewrite_overloads defs
    | [] -> []
  in

  Defs (rewrite_overloads defs)

(* Once we've specialized a definition, it's original valspec should
   be unused, unless another polymorphic function called it. We
   therefore remove all unused valspecs. Remaining polymorphic
   valspecs are then re-specialized. This process is iterated until
   the whole spec is specialized. *)

let initial_calls = ref (IdSet.of_list
  [ mk_id "main";
    mk_id "__SetConfig";
    mk_id "__ListConfig";
    mk_id "execute";
    mk_id "decode";
    mk_id "initialize_registers";
    mk_id "prop";
    mk_id "append_64" (* used to construct bitvector literals in C backend *)
  ])

let add_initial_calls ids = initial_calls := IdSet.union ids !initial_calls

let remove_unused_valspecs env ast =
  let calls = ref !initial_calls in
  let vs_ids = val_spec_ids ast in

  let inspect_exp = function
    | E_aux (E_app (call, _), _) as exp ->
       calls := IdSet.add call !calls;
       exp
    | exp -> exp
  in

  let rewrite_exp = { id_exp_alg with e_aux = (fun (exp, annot) -> inspect_exp (E_aux (exp, annot))) } in
  let _ = rewrite_defs_base { rewriters_base with rewrite_exp = (fun _ -> fold_exp rewrite_exp) } ast in

  let unused = IdSet.filter (fun vs_id -> not (IdSet.mem vs_id !calls)) vs_ids in

  let rec remove_unused (Defs defs) id =
    match defs with
    | def :: defs when is_fundef id def ->
       remove_unused (Defs defs) id
    | def :: defs when is_valspec id def ->
       remove_unused (Defs defs) id
    | DEF_overload (overload_id, overloads) :: defs ->
       begin
         match List.filter (fun id' -> Id.compare id id' <> 0) overloads with
         | [] -> remove_unused (Defs defs) id
         | overloads -> DEF_overload (overload_id, overloads) :: remove_unused (Defs defs) id
       end
    | def :: defs -> def :: remove_unused (Defs defs) id
    | [] -> []
  in

  List.fold_left (fun ast id -> Defs (remove_unused ast id)) ast (IdSet.elements unused)

let specialize_id spec id ast =
  let instantiations = instantiations_of spec id ast in
  let ast = specialize_id_valspec spec instantiations id ast in
  let ast = specialize_id_fundef instantiations id ast in
  specialize_id_overloads instantiations id ast

(* When we generate specialized versions of functions, we need to
   ensure that the types they are specialized to appear before the
   function definitions in the AST. Therefore we pull all the type
   definitions (and default definitions) to the start of the AST. *)
let reorder_typedefs (Defs defs) =
  let tdefs = ref [] in

  let rec filter_typedefs = function
    | (DEF_default _ | DEF_type _) as tdef :: defs ->
       tdefs := tdef :: !tdefs;
       filter_typedefs defs
    | def :: defs -> def :: filter_typedefs defs
    | [] -> []
  in

  let others = filter_typedefs defs in
  Defs (List.rev !tdefs @ others)

let specialize_ids keep_ids spec ids ast =
  let t = Profile.start () in
  let total = IdSet.cardinal ids in
  let _, ast =
    List.fold_left
      (fun (n, ast) id ->
        Util.progress "Specializing " (string_of_id id) n total; (n + 1, specialize_id spec id ast))
      (1, ast) (IdSet.elements ids)
  in
  let ast = reorder_typedefs ast in
  begin match !opt_ddump_spec_ast with
  | Some (f, i) ->
     let filename = f ^ "_spec_" ^ string_of_int i ^ ".sail" in
     let out_chan = open_out filename in
     Pretty_print_sail.pp_defs out_chan ast;
     close_out out_chan;
     opt_ddump_spec_ast := Some (f, i + 1)
  | None -> ()
  end;
  let ast, _ = Type_error.check Type_check.initial_env ast in
  let _, ast =
    List.fold_left
      (fun (n, ast) id ->
        Util.progress "Rewriting " (string_of_id id) n total;
        (n + 1, rewrite_polymorphic_calls spec id ast))
      (1, ast) (IdSet.elements ids)
  in
  let ast, env = Type_error.check Type_check.initial_env ast in
  initial_calls := keep_ids;
  let ast = remove_unused_valspecs env ast in
  Profile.finish "specialization pass" t;
  ast, env

let rec specialize_passes ?(keep_ids=(!initial_calls)) n spec env ast =
  if n = 0 then
    ast, env
  else
    let ids = polymorphic_functions spec ast in
    if IdSet.is_empty ids then
      ast, env
    else
      let ast, env = specialize_ids keep_ids spec ids ast in
      specialize_passes ~keep_ids (n - 1) spec env ast

let specialize = specialize_passes (-1)

let specialize_and_keep_funs keep_ids = specialize_passes ~keep_ids (-1)
