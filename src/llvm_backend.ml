module Big_int = Nat_big_num
module TC = Type_check

module StringSet = Set.Make(String)
module StringMap = Map.Make(String)

let opt_inst_mapping_fun = ref "encdec"
let opt_inst_info_fun = ref "get_inst_info"
let opt_td_inst_base = ref "HwInst"
let opt_td_prefix = ref ""
let opt_class_name = ref ""
let opt_namespace = ref ""
let opt_asm_mapping_fun = ref "assembly"
let opt_ast_typ = ref "ast"
let opt_regid_typ = ref "regid"
let opt_extimm_typ = ref "extimm"

type bit_field =
  | Bin_str of string
  | Hex_str of string
  | Name_str of string

type inst_field =
  | Fixed_bin_val of string
  | Fixed_hex_val of string
  | Op_field of (inst_op * (int * int)) list

and inst_subops =
  | No_subops
  | Field_concat of (bit_field * (int * int)) list
  | Op_tuple of inst_op list

and inst_op = {
  name : string;
  bit_size : int;
  subops : inst_subops;
  mapping : string
}

module Inst_op : sig
  type t = inst_op

  val compare : t -> t -> int

  val equal : t -> t -> bool
end = struct
  type t = inst_op

  let compare_tuple2 f1 f2 (t1, t2) (t1', t2') =
    let cmp = f1 t1 t1' in
    if cmp <> 0 then cmp else
      f2 t2 t2'

  let compare_list f l1 l2 =
    let rec go l1 l2 =
      match (l1, l2) with
      | (t1 :: l1, t2 :: l2) ->
          let cmp = f t1 t2 in
          if cmp <> 0 then cmp
            else go l1 l2
      | ([], []) -> 0
      | _ -> assert false
    in
    let cmp = List.compare_lengths l1 l2 in
    if cmp <> 0 then cmp else
      go l1 l2

  let compare_bit_field f1 f2 =
    match (f1, f2) with
    | (Bin_str b1 , Bin_str b2)  -> String.compare b1 b2
    | (Bin_str _  , Hex_str _)   -> -1
    | (Bin_str _  , Name_str _)  -> -2
    | (Hex_str _  , Bin_str _)   -> 1
    | (Hex_str b1 , Hex_str b2)  -> String.compare b1 b2
    | (Hex_str _  , Name_str _)  -> -1
    | (Name_str _ , Bin_str _)   -> 2
    | (Name_str _ , Hex_str _)   -> 1
    | (Name_str s1, Name_str s2) -> String.compare s1 s2

  let rec compare_inst_field f1 f2 =
    match (f1, f2) with
    | (Fixed_bin_val v1, Fixed_bin_val v2) -> String.compare v1 v2
    | (Fixed_bin_val _ , Fixed_hex_val _)  -> -1
    | (Fixed_bin_val _ , Op_field _)       -> -2
    | (Fixed_hex_val _ , Fixed_bin_val _)  -> 1
    | (Fixed_hex_val v1, Fixed_hex_val v2) -> String.compare v1 v2
    | (Fixed_hex_val _ , Op_field _)       -> -1
    | (Op_field _      , Fixed_bin_val _)  -> 2
    | (Op_field _      , Fixed_hex_val _)  -> 1
    | (Op_field l1     , Op_field l2)      ->
        let cmp_fun = compare_tuple2 compare_inst_op (compare_tuple2 compare compare) in
        compare_list cmp_fun l1 l2

  and compare_inst_subops op1 op2 =
    match (op1, op2) with
    | (No_subops       , No_subops)        -> 0
    | (No_subops       , Field_concat _)   -> -1
    | (No_subops       , Op_tuple _)       -> -2
    | (Field_concat _  , No_subops)        -> 1
    | (Field_concat fs1, Field_concat fs2) ->
        let cmp_fun = compare_tuple2 compare_bit_field (compare_tuple2 compare compare) in
        compare_list cmp_fun fs1 fs2
    | (Field_concat _  , Op_tuple _)       -> -1
    | (Op_tuple _      , No_subops)        -> 2
    | (Op_tuple _      , Field_concat _)   -> 1
    | (Op_tuple t1     , Op_tuple t2)      ->
        compare_list compare_inst_op t1 t2

  and compare_inst_op op1 op2 =
    let cmp = String.compare op1.name op2.name in
    if cmp <> 0 then cmp else
      let cmp = compare op1.bit_size op2.bit_size in
      if cmp <> 0 then cmp else
        let cmp = compare_inst_subops op1.subops op2.subops in
        if cmp <> 0 then cmp else
          String.compare op1.mapping op2.mapping

  let compare = compare_inst_op

  let equal a b = compare a b = 0
end

type inst_info_val =
  | IIV_bin of string
  | IIV_hex of string
  | IIV_nat of Big_int.num
  | IIV_str of string
  | IIV_enum of string
  | IIV_list of inst_info_val list

type inst_def = {
  name : string;
  bit_size : int;
  ops : inst_op list;
  fields : (inst_field * int) list;
  info : inst_info_val StringMap.t
}

type cpu_def = {
  insts : inst_def list;
  ops : inst_op list
}

type ctx = {
  tc_env : TC.Env.t;
  ctx_c : Jib_compile.ctx option;
  used_funs : Ast_util.IdSet.t;
  used_ctyps : Ast_util.IdSet.t;
  var_ctor_map : ((Ast.id * Jib.ctyp) list) Ast_util.Bindings.t;
  asm_mapping_funs : Ast_util.IdSet.t;
  ast_typs : Ast_util.IdSet.t;
  enum_ids : Ast_util.IdSet.t
}

module Option = struct
  let map = Util.option_map

  let bind opt f = Util.option_bind f opt

  let map_default f def opt =
    match opt with
    | Some v -> f v
    | None -> def
end

let string_of_id = Ast_util.string_of_id

let string_match r str =
  let r = Str.regexp ("^" ^ r ^ "$") in
  Str.string_match r str 0

let is_inst_mapping_fun id = string_match !opt_inst_mapping_fun (string_of_id id)

let is_inst_info_fun id = string_match !opt_inst_info_fun (string_of_id id)

let is_asm_mapping_fun id = string_match !opt_asm_mapping_fun (string_of_id id)

let is_ast_typ id = string_match !opt_ast_typ (string_of_id id)

let is_regid_typ id = string_match !opt_regid_typ (string_of_id id)

let is_extimm_typ id = string_match !opt_extimm_typ (string_of_id id)

let cpp_id name =
  if String.length !opt_namespace = 0 then
    name
  else
    PPrint.(string (!opt_namespace ^ "::") ^^ name)

let cpp_class_id ns name =
  if not ns || String.length !opt_class_name = 0 then
    name
  else
    PPrint.(string (!opt_class_name ^ "::") ^^ name)

let get_mpat_bit_size env mpat =
  let typ = TC.typ_of_mpat mpat in
  Option.bind (TC.destruct_vector env typ) (fun (nexp, _, typ) ->
    if Ast_util.is_bit_typ typ then
       TC.solve_unique env nexp |> Option.map Big_int.to_int
    else
      None
  )

let initial_ctx tc_env =
  { tc_env = tc_env
  ; ctx_c = None
  ; used_funs = Ast_util.IdSet.empty
  ; used_ctyps = Ast_util.IdSet.empty
  ; var_ctor_map = Ast_util.Bindings.empty
  ; asm_mapping_funs = Ast_util.IdSet.empty
  ; ast_typs = Ast_util.IdSet.empty
  ; enum_ids = Ast_util.IdSet.empty
  }

let get_cpu_def ctx (Ast.Defs defs) =
  let open Ast in

  let visited_ops = ref StringMap.empty in
  let unique_ops = ref [] in

  let proc_ast_pat mpat =
    let rec proc_op ops (MP_aux (pat, (l, _)) as mpat) =
      match pat with
      | MP_app (id, [pat]) when TC.Env.is_mapping id ctx.tc_env ->
          let [op] = proc_op [] pat in
          let op = { op with mapping = string_of_id id } in
          op :: ops
      | MP_app (id, [pat]) when TC.Env.is_union_constructor id ctx.tc_env ->
          let [op] = proc_op [] pat in
          let op =
              { op with
                name = string_of_id id
              ; subops =
                  match op.subops with
                  | No_subops -> Field_concat [(Name_str op.name, (0, op.bit_size - 1))]
                  | _ -> op.subops
              }
          in
          op :: ops
      | MP_app (_, _) ->
          let (name, subops) : string * inst_op list = proc_ast_pat' mpat in
          let new_op =
            { name = name
            ; bit_size = List.fold_left (fun sz (op : inst_op) -> sz + op.bit_size) 0 subops
            ; subops = if List.length subops = 0 then No_subops else Op_tuple subops
            ; mapping = ""
            }
          in
          new_op :: ops
      | MP_vector_concat vecs ->
          let rec proc_vec vecs (MP_aux (pat, (l, _)) as mpat) =
            match pat with
            | MP_lit (L_aux (L_bin bin, _)) ->
                (Bin_str bin, String.length bin) :: vecs
            | MP_lit (L_aux (L_hex bin, _)) ->
                (Hex_str bin, String.length bin * 4) :: vecs
            | MP_id id ->
              (
                match get_mpat_bit_size ctx.tc_env mpat with
                | Some size ->
                      let name = string_of_id id in
                      (Name_str name, size) :: vecs
                | _ -> raise (Reporting.err_general l "Failed to get bit size")
              )
            | MP_typ (mpat, _) ->
                proc_vec vecs mpat
            | _ -> raise (Reporting.err_general l "Unsupported pattern")
          in
          let (f, sz) :: vecs = List.fold_left proc_vec [] vecs in
          let size_to_range (((_, (_, hi)) :: _) as subops) (f, sz) = (f, (hi + 1, hi + sz)) :: subops in
          let subops = List.fold_left size_to_range [(f, (0, sz - 1))] vecs in
          let (_, (_, hi)) :: _ = subops in
          let new_op =
            { name = ""
            ; bit_size = hi + 1
            ; subops = Field_concat subops
            ; mapping = ""
            }
          in
          new_op :: ops
      | MP_id id ->
        (
          match get_mpat_bit_size ctx.tc_env mpat with
          | Some size ->
              let new_op =
                { name = string_of_id id
                ; bit_size = size
                ; subops = No_subops
                ; mapping = ""
                }
              in
              new_op :: ops
          | _ -> raise (Reporting.err_general l "Failed to get bit size")
        )
      | MP_typ (mpat, _) ->
          proc_op ops mpat
      | MP_lit (L_aux (L_unit, _)) ->
          ops
      | _ -> raise (Reporting.err_general l "Unsupported pattern")
    and proc_ast_pat' (MP_aux (pat, (l, _))) =
      match pat with
      | MP_app (id, ops) when TC.Env.is_union_constructor id ctx.tc_env ->
          let name = string_of_id id in
          let ops = List.fold_left proc_op [] ops |> List.rev in
          (
            let rec check_and_collect_ops ops =
              match ops with
              | (op' : inst_op) :: ops ->
                let op =
                  let subops =
                    match op'.subops with
                    | No_subops | Op_tuple _ -> op'.subops
                    | Field_concat fs ->
                        let fs = List.filter (fun (f, _) ->
                            match f with
                            | Bin_str _ | Hex_str _ -> true
                            | Name_str _ -> false
                          ) fs
                        in
                        if List.length fs = 0 then
                          No_subops
                        else
                          Field_concat fs
                  in
                  { op' with subops = subops }
                in
                (
                  match op.subops with
                  | Op_tuple subops -> check_and_collect_ops subops
                  | _ -> ()
                );
                (
                  if String.length op.name = 0 then
                    raise (Reporting.err_general l ("Found unnamed operand"))
                  else
                    if StringMap.mem op.name !visited_ops then
                      let old = StringMap.find op.name !visited_ops in
                      if Inst_op.equal op old then
                        check_and_collect_ops ops
                      else
                        raise (Reporting.err_general l (op.name ^ " is inconsistent"))
                    else (
                      visited_ops := StringMap.add op.name op !visited_ops;
                      unique_ops := op :: !unique_ops;
                      check_and_collect_ops ops
                    )
                )
              | [] -> ()
            in
            check_and_collect_ops ops;
            (name, ops)
          )
      | _ -> raise (Reporting.err_general l "Expected union constructor pattern")
    in
    proc_ast_pat' mpat
  in

  let proc_inst_pat ops (MP_aux (pat, (l, _)) as mpat) =
    let rec proc_vec fields (MP_aux (pat, (l, _)) as mpat) =
      match get_mpat_bit_size ctx.tc_env mpat with
      | Some size ->
        (
          match pat with
          | MP_lit (L_aux (L_bin bin, _)) ->
              (Fixed_bin_val bin, size) :: fields
          | MP_lit (L_aux (L_hex hex, _)) ->
              (Fixed_hex_val hex, size) :: fields
          | MP_id id ->
              let field_name = string_of_id id in
              let rec find_ops root_op (op : inst_op) (assoc_ops, lo) =
                if field_name = op.name then
                  let assoc_ops = (root_op, (lo, lo + op.bit_size - 1)) :: assoc_ops in
                  (assoc_ops, lo + op.bit_size)
                else
                  match op.subops with
                  | No_subops -> (assoc_ops, lo + op.bit_size)
                  | Field_concat subops ->
                      let assoc_ops = List.fold_right (fun (bf, (local_lo, local_hi)) assoc_ops ->
                          match bf with
                          | Name_str fname when fname = field_name ->
                              (root_op, (local_lo + lo, local_hi + lo)) :: assoc_ops
                          | _ -> assoc_ops
                        ) subops assoc_ops
                      in
                      (assoc_ops, lo + op.bit_size)
                  | Op_tuple subops ->
                      List.fold_right (find_ops root_op) subops (assoc_ops, lo)
              in
              let assoc_ops = List.fold_right (fun op assoc_ops ->
                  let (assoc_ops, _) = find_ops op op (assoc_ops, 0) in
                  assoc_ops
                ) ops []
              in
              (Op_field assoc_ops, size) :: fields
          | MP_typ (mpat, _) ->
              proc_vec fields mpat
          | _ -> raise (Reporting.err_general l "Unsupported pattern")
        )
      | _ -> raise (Reporting.err_general l "Failed to get bit size")
    in
    let get_inst_size mpat =
      match get_mpat_bit_size ctx.tc_env mpat with
      | Some size -> size
      | None -> raise (Reporting.err_general l "Invalid mapping function")
    in
    match pat with
    | MP_vector_concat vecs ->
        let size = get_inst_size mpat in
        let fields = List.fold_left proc_vec [] vecs |> List.rev in
        (size, fields)
    | _ -> raise (Reporting.err_general l "Unsupported pattern")
  in
  let proc_mapcl info (MCL_aux (mapcl, (l, _))) =
    match mapcl with
    | MCL_bidir (MPat_aux (MPat_when (l_mp, _), _), MPat_aux (MPat_when (r_mp, _), _))
    | MCL_bidir (MPat_aux (MPat_pat l_mp, _), MPat_aux (MPat_pat r_mp, _)) ->
        let (name, ops) = proc_ast_pat l_mp in
        let (size, fields) = proc_inst_pat ops r_mp in
        let inst =
          { name = name
          ; bit_size = size
          ; ops = ops
          ; fields = fields
          ; info = StringMap.empty
          }
        in
        inst :: info
    | _ -> raise (Reporting.err_general l "Expected bidirectional mapping")
  in
  let proc_mapdef info def =
    match def with
    | DEF_mapdef (MD_aux (MD_mapping (id, _, mapcls), (l, _))) ->
        if is_inst_mapping_fun id then
          List.fold_left proc_mapcl info mapcls
        else
          info
    | _ -> info
  in

  let collect_inst_info inst_map def =
    let proc_funcl inst_map (FCL_aux (FCL_Funcl (id, (Pat_aux (pexp, (l, _)))), _)) =
      let get_inst_name (P_aux (pat, (l, _))) =
        match pat with
        | P_app (id, _) when TC.Env.is_union_constructor id ctx.tc_env -> string_of_id id
        | _ -> raise (Reporting.err_general l "Expected union pattern matching")
      in
      let get_info (E_aux (exp, (l, _))) =
        match exp with
        | E_record fexps ->
            let rec info_val_of_exp (E_aux (exp, (l, _)) as exp_aux) =
              match exp with
              | E_lit (L_aux (lit, _)) ->
                  (match lit with
                  | L_bin b -> IIV_bin b
                  | L_hex h -> IIV_hex h
                  | L_num n -> IIV_nat n
                  | L_string s -> IIV_str s
                  | _ -> raise (Reporting.err_general l "Unsupported literal"))
              | E_id id ->
                  (match TC.Env.lookup_id id ctx.tc_env with
                  | Ast_util.Enum _ -> IIV_enum (string_of_id id)
                  | _ -> raise (Reporting.err_general l "Unsupported type"))
              | E_list es ->
                  IIV_list (List.fold_right (fun e vs -> info_val_of_exp e :: vs) es [])
              | _ ->
                  raise (Reporting.err_general l "Unsupported expression")
            in
            let collect map (FE_aux (FE_Fexp (id, exp), _)) =
              StringMap.add (string_of_id id) (info_val_of_exp exp) map
            in
            List.fold_left collect StringMap.empty fexps
        | _ -> raise (Reporting.err_general l "Expected struct expression")
      in
      if is_inst_info_fun id then
        match pexp with
        | Pat_exp (pat, exp)
        | Pat_when (pat, _, exp) ->
            let name = get_inst_name pat in
            let info = get_info exp in
            StringMap.update name (function
              | Some inst -> Some { inst with info = info }
              | None -> raise (Reporting.err_general l ("Failed to find instruction definition: " ^ name))
            ) inst_map
      else
        inst_map
    in
    match def with
    | DEF_fundef (FD_aux (FD_function (_, _, _, funcls), _)) ->
        List.fold_left proc_funcl inst_map funcls
    | _ -> inst_map
  in

  let insts = List.fold_left proc_mapdef [] defs in
  let inst_map = List.fold_left (fun map inst -> StringMap.add inst.name inst map) StringMap.empty insts in
  let inst_map = List.fold_left collect_inst_info inst_map defs in
  let insts = List.map (fun (_, i) -> i) (StringMap.bindings inst_map) in
  { insts = insts
  ; ops = List.rev !unique_ops
  }

(* tablegen printer *)

module PP_td = struct
  open PPrint

  let vsep = separate hardline

  let hsep_comma = separate (comma ^^ space)

  let decl_rec ty name args classes contents =
    (ty ^^ space ^^ name) |> (
      if List.length args = 0 then
        fun doc -> doc
      else
        fun doc -> doc ^^ (angles @@ hsep_comma args)
    ) |> (
      if List.length classes = 0 then
        fun doc -> doc
      else
        fun doc -> doc ^^ space ^^ colon ^^ space ^^ hsep_comma classes
    ) |> (
      if List.length contents = 0 then
        fun doc -> doc ^^ semi
      else
        fun doc ->
          let stmts = List.map (fun stmt -> stmt ^^ semi) contents in
          doc ^^ space ^^ vsep [nest 2 @@ vsep (lbrace :: stmts); rbrace]
    ) |> (fun doc -> doc ^^ hardline)

  let def name = decl_rec (string "def") name []

  let class_ = decl_rec (string "class")

  let multiclass = decl_rec (string "multiclass")

  let class_instance name args =
    if List.length args = 0 then
      name
    else
      name ^^ (angles @@ hsep_comma args)

  let decl_field_ ty name value =
    (ty ^^ space ^^ name) |> (fun doc ->
      match value with
      | Some v -> doc ^^ space ^^ equals ^^ space ^^ v
      | None -> doc
    )

  let decl_field ty name value = decl_field_ ty name (Some value)

  let decl_field' ty name = decl_field_ ty name None

  let let_ = decl_field (string "let")

  let bits_ n = decl_field_ (string "bits" ^^ (angles @@ string @@ string_of_int n))

  let bits n name value = bits_ n name (Some value)

  let bits' n name = bits_ n name None

  let string_t_ n = decl_field_ (string "string")

  let string_t n name value = string_t_ n name (Some value)

  let string_t' n name = string_t_ n name None

  let dag_ n = decl_field_ (string "dag")

  let dag n name value = dag_ n name (Some value)

  let dag' n name = dag_ n name None

  let field f = string "field" ^^ space ^^ f

  let bit_val name n = name ^^ braces (string @@ string_of_int n)

  let bit_seq name n1 n2 = name ^^ braces ((string @@ string_of_int n1) ^^ minus ^^ (string @@ string_of_int n2))

  let dag_val name vals = parens (name |>
    if List.length vals = 0 then
      fun doc -> doc
    else
      fun doc -> doc ^^ space ^^ hsep_comma vals
  )

  let code_val c = brackets @@ braces c

  let list_val vals = brackets (
    if List.length vals = 0 then
      empty
    else
      hsep_comma vals
  )

  let str_lit s = dquotes (string s)

  let bit_lit b = string ("0b" ^ b)

  let hex_lit b = string ("0x" ^ b)

  let int_lit n = string (Big_int.to_string n)
end

(* instrinfo and operands *)

let gen_instrinfo cpu =
  let open PPrint in
  let open PP_td in

  let gen_class inst =
    let base_class = string !opt_td_inst_base in
    let inst_size = string @@ string_of_int inst.bit_size in
    let inheritance = class_instance (base_class ^^ inst_size) [string "outs"; string "ins"; string "pattern"] in
    let record_name = string (!opt_td_prefix ^ inst.name) in

    let decls =
      let gen_decl (op : inst_op) decls =
        let decl = bits' op.bit_size (string op.name) in
        let rec gen_inits (root_op : inst_op) op (inits, lo) =
          match op.subops with
          | No_subops -> (inits, lo + op.bit_size)
          | Field_concat subops ->
              let inits =
                List.fold_right (fun (bf, (local_lo, local_hi)) inits ->
                  let lit =
                    match bf with
                    | Bin_str s -> Some (bit_lit s)
                    | Hex_str s -> Some (hex_lit s)
                    | _ -> None
                  in
                  Option.map_default (fun lit ->
                    let init = let_ (bit_seq (string root_op.name) (local_hi + lo) (local_lo + lo)) lit in
                    init :: inits
                  ) inits lit
                ) subops inits
              in
              (inits, lo + op.bit_size)
          | Op_tuple subops ->
              List.fold_right (gen_inits root_op) subops (inits, lo)
        in
        let (inits, _) = gen_inits op op ([], 0) in
        [decl] @ inits @ decls
      in
      List.fold_right gen_decl inst.ops []
    in

    let stmts =
      let gen_field (f, size) (lo, stmts) =
        let hi = lo + size - 1 in
        let set_inst = let_ (bit_seq (string "Inst") hi lo) in
        let set_ops =
          match f with
          | Fixed_bin_val v -> [set_inst @@ bit_lit v]
          | Fixed_hex_val v -> [set_inst @@ hex_lit v]
          | Op_field ops ->
              let set ((op : inst_op), (lo, hi)) = set_inst @@ bit_seq (string op.name) hi lo in
              List.map set ops
        in
        (hi + 1, set_ops @ stmts)
      in
      let (_, stmts) = List.fold_right gen_field inst.fields (0, []) in
      stmts
    in
    let stmts = List.fold_left (fun stmts (k, v) ->
        let rec pp_info_val = function
          | IIV_bin b -> bit_lit b
          | IIV_hex h -> hex_lit h
          | IIV_nat n -> int_lit n
          | IIV_str s -> str_lit s
          | IIV_enum e -> string e
          | IIV_list vs -> list_val (List.map pp_info_val vs)
        in
        let_ (string k) (pp_info_val v) :: stmts
      ) stmts (List.rev (StringMap.bindings inst.info))
    in

    class_
      (underscore ^^ record_name)
      [ string "dag" ^^ space ^^ string "outs"
      ; string "dag" ^^ space ^^ string "ins"
      ; string "list<dag>" ^^ space ^^ string "pattern"
      ]
      [inheritance]
      (decls @ stmts)
  in
  let gen_def inst =
    let record_name = string (!opt_td_prefix ^ inst.name) in
    let ops =
      let gen_op_str (op : inst_op) = string (!opt_td_prefix ^ op.name ^ "_op:$" ^ op.name) in
      List.map gen_op_str inst.ops
    in
    def record_name
      [ class_instance
          (underscore ^^ record_name)
          [ dag_val (string "outs") []
          ; dag_val (string "ins") ops
          ; list_val []
          ]
      ]
      []
  in
  vsep @@ List.concat @@ List.map (fun inst -> [gen_class inst; gen_def inst]) cpu.insts

let gen_operands cpu =
  let open PPrint in
  let open PP_td in

  let gen_op (op : inst_op) =
    let prefix = !opt_td_prefix ^ op.name in
    let op_name = prefix ^ "_op" in
    let subops =
      match op.subops with
      | Op_tuple subops -> List.map (fun (op : inst_op) -> string (!opt_td_prefix ^ op.name ^ "_op")) subops
      | _ -> []
    in
    [ def (string (op_name))
        [class_instance (string "Operand") [string "i32"]]
        (
          (
            if List.length subops = 0 then
              []
            else
              [let_ (string "MIOperandInfo") (dag_val (string "op") subops)]
          ) @
          [ let_ (string "EncoderMethod") (str_lit ("encode_" ^ op_name))
          ; let_ (string "DecoderMethod") (str_lit ("decode_" ^ op_name))
          ]
        )
    ]
  in
  vsep @@ List.concat @@ List.map gen_op cpu.ops

let pp_doc out doc =
  let pp = PPrint.ToChannel.pretty 1. 120 in
  match out with
  | Some file ->
      let out = open_out file in
      pp out doc;
      close_out out
  | None ->
      pp stdout doc

let output_instrinfo_td out ctx ast =
  let cpu = get_cpu_def ctx ast in
  let doc = gen_instrinfo cpu in
  pp_doc out doc

let output_operands_td out ctx ast =
  let cpu = get_cpu_def ctx ast in
  let doc = gen_operands cpu in
  pp_doc out doc

(* bytecode printer *)

let is_ast_ctyp ctyp =
  let open Jib in
  match ctyp with
  | CT_variant (id, _) -> is_ast_typ id
  | _ -> false

let is_regid_ctyp ctyp =
  let open Jib in
  match ctyp with
  | CT_enum (id, _) -> is_regid_typ id
  | _ -> false

let is_extimm_ctyp ctyp =
  let open Jib in
  match ctyp with
  | CT_variant (id, _) -> is_extimm_typ id
  | _ -> false

let get_tuple_field str =
  if string_match "ztup\\([0-9]+\\)" str then
    Some (Str.matched_group 1 str)
  else
    None

let v_mask_lower i =
  let open Jib in
  let open Value2 in
  V_lit (VL_bits (Util.list_init i (fun _ -> Sail2_values.B1), true), CT_fbits (i, true))

module PP_bytecode : sig
  type printers = {
    ctx : ctx;
    pp_ctyp : printers -> bool -> Jib.ctyp -> PPrint.document;
    pp_clexp : printers -> Jib.clexp -> PPrint.document;
    pp_cval : printers -> Jib.cval -> PPrint.document;
    pp_cval_param : printers -> Jib.cval -> PPrint.document;
    pp_assign : printers -> Jib.clexp -> Jib.cval -> PPrint.document;
    pp_instr : printers -> Jib.instr -> PPrint.document;
  }

  val printers_base : ctx -> printers
  val pp_block : PPrint.document -> PPrint.document
  val pp_id : Ast.id -> PPrint.document
  val pp_value : Value2.vl -> PPrint.document
  val pp_ctyp : printers -> bool -> Jib.ctyp -> PPrint.document
  val pp_clexp : printers -> Jib.clexp -> PPrint.document
  val pp_cval : printers -> Jib.cval -> PPrint.document
  val pp_cval_param : printers -> Jib.cval -> PPrint.document
  val pp_assign : printers -> Jib.clexp -> Jib.cval -> PPrint.document
  val pp_instr : printers -> Jib.instr -> PPrint.document
end  = struct
  open Jib
  open PPrint

  type printers = {
    ctx : ctx;
    pp_ctyp : printers -> bool -> ctyp -> document;
    pp_clexp : printers -> clexp -> document;
    pp_cval : printers -> cval -> document;
    pp_cval_param : printers -> cval -> document;
    pp_assign : printers -> clexp -> cval -> document;
    pp_instr : printers -> instr -> document;
  }

  let pp_block doc =
    nest 4 (lbrace ^^ hardline ^^ doc) ^^ hardline ^^ rbrace

  let pp_id id = string (Util.zencode_string (string_of_id id))

  let pp_value v =
    let open Value2 in
    string (match v with
      | VL_bits ([], _) -> "0"
      | VL_bits (bs, _) -> Sail2_values.show_bitlist bs
      | VL_int i -> Big_int.to_string i
      | VL_bool true -> "true"
      | VL_bool false -> "false"
      | VL_null -> "nullptr"
      | VL_unit -> "sail::UNIT"
      | VL_bit Sail2_values.B0 -> "0"
      | VL_bit Sail2_values.B1 -> "1"
      | VL_string str -> "\"" ^ str ^ "\""
      | _ -> failwith "Unsupported value"
    )

  let pp_ctyp pp = pp.pp_ctyp pp
  let pp_clexp pp = pp.pp_clexp pp
  let pp_cval pp = pp.pp_cval pp
  let pp_cval_param pp = pp.pp_cval_param pp
  let pp_assign pp = pp.pp_assign pp
  let pp_instr pp = pp.pp_instr pp

  let base_pp_ctyp pp ns ctyp =
    match ctyp with
    | CT_bool -> string "bool"
    | CT_unit -> string "sail::Unit"
    | CT_string -> string "std::string"

    | CT_fint _
    | CT_lint -> string "std::int64_t"

    | CT_bit -> string "std::uint32_t"
    | CT_fbits _ -> string "std::uint64_t"
    | CT_sbits _
    | CT_lbits _ -> string "sail::BitVec"

    | CT_enum _ -> string "unsigned"
    | CT_variant (id, _) -> cpp_class_id ns (pp_id id)
    | CT_tup ctyps ->
      (
        match ctyps with
        | [] -> pp_ctyp pp ns CT_unit
        | [t] -> pp_ctyp pp ns t
        | _ -> string "std::tuple" ^^ angles (separate_map (comma ^^ space) (pp_ctyp pp ns) ctyps)
      )
    | CT_list ctyp -> string "std::list" ^^ angles (pp_ctyp pp ns ctyp)
    | CT_ref ctyp -> pp_ctyp pp ns ctyp ^^ space ^^ star

    | _ -> failwith "Unsupported type"

  let base_pp_cval pp cval =
    match cval with
    | V_id (Name (id, _), _) ->
        if Ast_util.IdSet.mem id pp.ctx.enum_ids then
          cpp_id (string (string_of_id id))
        else
          pp_id id
    | V_lit (v, _) -> pp_value v
    | V_call (op, cvals) -> (
        match (op, cvals) with
        | (Bit_to_bool, [v]) ->
            parens (parens (string "bool") ^^ pp_cval pp v)
        | (Bnot, [v]) ->
            bang ^^ parens (pp_cval pp v)
        | (Eq, [v1; v2]) ->
            parens (pp_cval pp v1 ^^ string " == " ^^ pp_cval pp v2)
        | (Neq, [v1; v2]) ->
            parens (pp_cval pp v1 ^^ string " != " ^^ pp_cval pp v2)
        | (Ilt, [v1; v2]) ->
            parens (pp_cval pp v1 ^^ string " < " ^^ pp_cval pp v2)
        | (Igt, [v1; v2]) ->
            parens (pp_cval pp v1 ^^ string " > " ^^ pp_cval pp v2)
        | (Ilteq, [v1; v2]) ->
            parens (pp_cval pp v1 ^^ string " <= " ^^ pp_cval pp v2)
        | (Igteq, [v1; v2]) ->
            parens (pp_cval pp v1 ^^ string " >= " ^^ pp_cval pp v2)
        | (Iadd, [v1; v2]) ->
            parens (pp_cval pp v1 ^^ string " + " ^^ pp_cval pp v2)
        | (Isub, [v1; v2]) ->
            parens (pp_cval pp v1 ^^ string " - " ^^ pp_cval pp v2)
        | (Unsigned 64, [vec]) ->
            parens (parens (string "std::uint64_t") ^^ pp_cval pp vec)
        | (Signed 64, [vec]) ->
            parens (parens (string "std::int64_t") ^^ pp_cval pp vec)
        | (Bvand, [v1; v2]) ->
            parens (pp_cval pp v1 ^^ string " & " ^^ pp_cval pp v2)
        | (Bvor, [v1; v2]) ->
            parens (pp_cval pp v1 ^^ string " | " ^^ pp_cval pp v2)
        | (Bvxor, [v1; v2]) ->
            parens (pp_cval pp v1 ^^ string " ^ " ^^ pp_cval pp v2)
        | _ ->
          failwith "Could not generate cval primop"
      )
    | V_field (f, field) ->
        pp_cval pp f ^^ dot ^^ string field
    | V_tuple_member (f, _, n) ->
        string "std::get" ^^ angles (string (string_of_int n)) ^^ parens (pp_cval pp f)
    | V_ctor_kind (f, ctor, [], _) ->
        pp_cval pp f ^^ string (".kind != Kind_" ^ Util.zencode_string (string_of_id ctor))
    | V_ctor_kind (f, ctor, unifiers, _) ->
        let kind = string_of_id ctor ^ "_" ^ Util.string_of_list "_" Jib_util.string_of_ctyp unifiers in
        pp_cval pp f ^^ string (".kind != Kind_" ^ Util.zencode_string kind)
    | V_ctor_unwrap (ctor, f, [], _) ->
        pp_cval pp f ^^ dot ^^ string (Util.zencode_string (string_of_id ctor))
    | V_ctor_unwrap (ctor, f, unifiers, _) ->
        let kind = string_of_id ctor ^ "_" ^ Util.string_of_list "_" Jib_util.string_of_ctyp unifiers in
        pp_cval pp f ^^ dot ^^ string (Util.zencode_string kind)
    | _ -> failwith ("Unsupported cval: " ^ Jib_util.string_of_cval cval)

  let base_pp_cval_param pp cval =
    match Jib_util.cval_ctyp cval with
    | CT_fbits (len, _) -> pp_cval pp cval ^^ comma ^^ space ^^ string (string_of_int len)
    | _ -> pp_cval pp cval

  let base_pp_clexp pp clexp =
    match clexp with
    | CL_id (Name (id, _), _) -> pp_id id
    | CL_field (clexp, f) -> parens (pp_clexp pp clexp) ^^ dot ^^ string f
    | CL_addr clexp -> star ^^ pp_clexp pp clexp
    | CL_tuple (clexp, n) -> string "std::get" ^^ angles (string (string_of_int n)) ^^ parens (pp_clexp pp clexp)
    | _ -> failwith ("Unsupported l-exp")

  let rec base_pp_assign pp clexp cval =
    let ctyp_to = Jib_util.clexp_ctyp clexp in
    let ctyp_from = Jib_util.cval_ctyp cval in
    let assign cval = pp_clexp pp clexp ^^ space ^^ equals ^^ space ^^ cval ^^ semi in
    match (ctyp_to, ctyp_from) with
    | (_, _) when  Jib_util.ctyp_equal ctyp_to ctyp_from ->
        assign (pp_cval pp cval)
    | (CT_tup ctyps_to, CT_tup ctyps_from) when List.length ctyps_to = List.length ctyps_from ->
        let len = List.length ctyps_to in
        let conversions =
          List.mapi (
            fun i ctyp -> pp_assign pp (CL_tuple (clexp, i)) (V_tuple_member (cval, len, i))
          ) ctyps_from
        in
        string "  /* conversions */" ^^ hardline ^^
        separate hardline conversions ^^ hardline ^^
        string "  /* end conversions */"
    | (_, _) ->
        let ctyp = pp_ctyp pp false ctyp_to in
        let params = pp_cval_param pp cval in
        assign (ctyp ^^ parens params)

  let rec base_pp_instr pp (I_aux (instr, _) as cinstr) =
    match instr with
    | I_decl (ctyp, Name (id, _))
    | I_reset (ctyp, Name (id, _)) ->
        pp_ctyp pp false ctyp ^^ space ^^ pp_id id ^^ semi
    | I_init (ctyp, id, cval)
    | I_reinit (ctyp, id, cval) ->
        let clexp = CL_id (id, ctyp) in
        pp_ctyp pp false ctyp ^^ space ^^ pp_assign pp clexp cval
    | I_clear (_, Name (id, _)) ->
        string "/* kill " ^^ pp_id id ^^ string " */"
    | I_copy (clexp, cval) -> (
        match clexp with
        | CL_id (Return _, _) -> string "return" ^^ space ^^ pp_cval pp cval ^^ semi
        | _ -> pp_assign pp clexp cval
      )
    | I_jump (cval, label) ->
        string "if " ^^ parens (pp_cval pp cval) ^^ space ^^
        string "goto " ^^ string label ^^ semi
    | I_if (cval, then_instrs, [], _) ->
        string "if " ^^ parens (pp_cval pp cval) ^^ hardline ^^
        pp_instr_block pp then_instrs
    | I_if (cval, then_instrs, else_instrs, _) ->
        string "if " ^^ parens (pp_cval pp cval) ^^ hardline ^^
        pp_instr_block pp then_instrs ^^ hardline ^^
        string "else" ^^ hardline ^^
        pp_instr_block pp else_instrs
    | I_block instrs ->
        pp_instr_block pp instrs
    | I_funcall (clexp, extern, f, args) ->
        let fun_call f param =
          let pp_cval = if param then pp_cval_param else pp_cval in
          f ^^ parens (separate_map (comma ^^ space) (pp_cval pp) args) in
        let op_call op =
          match args with
          | [l; r] -> parens (pp_cval pp l ^^ space ^^ op ^^ space ^^ pp_cval pp r)
          | _ -> assert false
        in
        let call =
          let fname = string_of_id f in
          match fname with
          | "eq_int"
          | "eq_bits" -> op_call (equals ^^ equals)
          | "sub_nat" -> op_call minus
          | "bitvector_access" -> fun_call (string "bitvecAccess") true
          | "bitvector_concat" -> fun_call (string "bitvecConcat") true
          | "vector_subrange" -> fun_call (string "bitvecSubrange") true
          | _ ->
              let f =
                if TC.Env.is_extern f pp.ctx.tc_env "llvm" then
                  string (TC.Env.get_extern f pp.ctx.tc_env "llvm")
                else if extern then
                  string fname
                else
                  pp_id f
              in
              fun_call f false
        in
        let lexp =
          match clexp with
          | CL_id (Return _, _) -> string "return"
          | _ -> pp_clexp pp clexp ^^ space ^^ equals
        in
        lexp ^^ space ^^ call ^^ semi
    | I_match_failure ->
        string "llvm_unreachable(\"match_failure\");"
    | I_undefined _ ->
        string "llvm_unreachable(\"undefined\");"
    | I_comment s ->
        string ("/* " ^ s ^ " */")
    | I_label label ->
        string label ^^ colon
    | I_goto label ->
        string "goto " ^^ string label ^^ semi
    | I_end _ ->
        empty
    | _ ->
        failwith "Unsupported instr"

  and pp_instr_block pp instrs =
    let open PPrint in
    match instrs with
    | [] -> assert false
    | _ ->
        pp_block (separate_map hardline (pp_instr pp) instrs)

  let printers_base ctx =
    { ctx = ctx
    ; pp_ctyp = base_pp_ctyp
    ; pp_clexp = base_pp_clexp
    ; pp_cval = base_pp_cval
    ; pp_cval_param = base_pp_cval_param
    ; pp_assign = base_pp_assign
    ; pp_instr = base_pp_instr
    }
end

let collect_fun_typ_ids ctx (Ast.Defs defs) =
  let open Ast in
  let open Ast_util in

  let go ctx = function
    | DEF_mapdef (MD_aux (MD_mapping (id, _, _), _)) ->
        if is_asm_mapping_fun id then
          { ctx with asm_mapping_funs = IdSet.add id ctx.asm_mapping_funs }
        else
          ctx
    | DEF_type (TD_aux (TD_variant (id, _, _, _), _)) when is_ast_typ id ->
        { ctx with ast_typs = IdSet.add id ctx.ast_typs }
    | DEF_type (TD_aux (TD_enum (_, members, _), _)) ->
        let add enums id = IdSet.add id enums in
        { ctx with enum_ids = List.fold_left add ctx.enum_ids members }
    | _ -> ctx
  in
  List.fold_left go ctx defs

let find_used_funs tc_env ast entries =
  let open Ast_util in

  let fundef_map =
    let open Rewriter in
    let open Ast in

    let map = ref Bindings.empty in
    let rewrite_fun = function
      | FD_aux (FD_function (_, _, _, ((FCL_aux (FCL_Funcl (id, _), _)) as funcl)::_), _) as fundef ->
          map := Bindings.add id fundef !map;
          fundef
      | fundef -> fundef
    in
    (
      ignore (rewrite_defs_base { rewriters_base with rewrite_fun = fun _ -> rewrite_fun } ast);
      !map
    )
  in

  let next_funs = ref entries in
  let visited = ref IdSet.empty in
  let rec go () =
    if IdSet.is_empty !next_funs then
      ()
    else
      let id = IdSet.min_elt !next_funs in
      (
        next_funs := IdSet.remove id !next_funs;
        if IdSet.mem id !visited then
          ()
        else
        (
          let open Rewriter in
          let open Ast in
          match Bindings.find_opt id fundef_map with
          | Some fundef ->
              let inspect_exp = function
                | E_aux (E_app (call, _), _) as exp when not (TC.Env.is_union_constructor call tc_env) ->
                    if Bindings.mem call fundef_map then
                      next_funs := IdSet.add call !next_funs
                    else
                      ();
                    exp
                | exp -> exp
              in
              let rewrite_exp = { id_exp_alg with e_aux = (fun (exp, annot) -> inspect_exp (E_aux (exp, annot))) } in
              (
                ignore (rewrite_fun { rewriters_base with rewrite_exp = (fun _ -> fold_exp rewrite_exp) } fundef);
                visited := IdSet.add id !visited
              )
          | None ->
              if TC.Env.is_extern id tc_env "llvm" then
                visited := IdSet.add id !visited
              else
                let msg = "Failed to find function: " ^ string_of_id id in
                raise (Reporting.err_general Parse_ast.Unknown msg)
        );
        go ()
      )
  in
  (
    go ();
    !visited
  )

let rec move_decls_to_head instrs =
  let open Jib in
  let go (vars, others) ((I_aux (instr, annot)) as cinstr) =
    match instr with
    | I_decl _ | I_reset _ ->
        (cinstr :: vars, others)
    | I_if (cond, t, f, typ) ->
        let t' = move_decls_to_head t in
        let f' = move_decls_to_head f in
        (vars, I_aux (I_if (cond, t', f', typ), annot) :: others)
    | I_block is ->
        let is' = move_decls_to_head is in
        (vars, I_aux (I_block is', annot) :: others)
    | I_try_block is ->
        let is' = move_decls_to_head is in
        (vars, I_aux (I_try_block is', annot) :: others)
    | _ ->
        (vars, cinstr :: others)
  in
  let (vars, others) = List.fold_left go ([], []) instrs in
  List.rev vars @ List.rev others

let cdef_map_instrs f =
  let open Jib in
  let go cdef =
    match cdef with
    | CDEF_reg_dec (id, ctyp, instrs) -> CDEF_reg_dec (id, ctyp, f instrs)
    | CDEF_let (n, bindings, instrs) -> CDEF_let (n, bindings, f instrs)
    | CDEF_fundef (id, heap_return, args, instrs) -> CDEF_fundef (id, heap_return, args, f instrs)
    | CDEF_startup (id, instrs) -> CDEF_startup (id, f instrs)
    | CDEF_finish (id, instrs) -> CDEF_finish (id, f instrs)
    | _ -> cdef
  in
  List.map go

let get_fundef_typ ctx id =
  let (_, Typ_aux (fn_typ, _)) = TC.Env.get_val_spec id ctx.tc_env in
  match fn_typ with
  | Typ_fn (arg_typs, ret_typ, _) -> (arg_typs, ret_typ)
  | _ -> assert false

let ctyp_of_typ ctx typ =
  let ctx =
    match ctx.ctx_c with
    | Some c -> c
    | None -> assert false
  in
  C_backend.ctyp_of_typ ctx typ

let compile_ast ctx ast entries =
  let open Ast_util in
  let open Jib in

  let (ast_c, tc_env) = Process_file.rewrite_ast_target "c" ctx.tc_env ast in
  let used_funs = find_used_funs ctx.tc_env ast_c entries in
  let keep_ids = IdSet.add (mk_id "instantiate_variant_constructors") used_funs in

  let (ast_c, tc_env) = Specialize.(specialize_and_keep_funs keep_ids typ_ord_specialization ctx.tc_env ast_c) in
  let (ast_c, tc_env) = Specialize.(specialize_passes ~keep_ids:keep_ids 2 int_specialization tc_env ast_c) in
  let (cdefs, ctx_c) = C_backend.jib_of_ast tc_env ast_c in

  let ctx =
    { ctx with
      tc_env = ctx_c.tc_env
    ; ctx_c = Some ctx_c
    ; used_funs = used_funs
    }
  in

  let cdefs = cdef_map_instrs move_decls_to_head cdefs in
  let used_ctyps =
    let open Jib_util in
    let go ids = function
      | CDEF_fundef (id, _, _, instrs) when IdSet.mem id used_funs ->
          let (arg_typs, ret_typ) = get_fundef_typ ctx id in
          let ctyps = List.fold_left (fun s typ ->
              CTSet.add (ctyp_of_typ ctx typ) s
            ) CTSet.empty (ret_typ :: arg_typs)
          in
          let ctyps = CTSet.union (instrs_ctyps instrs) ctyps in
          CTSet.fold (fun ctyp ids -> IdSet.union (ctyp_ids ctyp) ids) ctyps ids
      | _ -> ids
    in
    List.fold_left go IdSet.empty cdefs
  in
  let var_map =
    let go map = function
      | CDEF_type (CTD_variant (id, ctors)) when IdSet.mem id used_ctyps ->
          Bindings.add id ctors map
      | _ -> map
    in
    List.fold_left go Bindings.empty cdefs
  in

  let ctx =
    { ctx with
      used_ctyps = used_ctyps
    ; var_ctor_map = var_map
    }
  in
  (cdefs, ctx)

let doc_header =
  let open PPrint in
  separate_map hardline string
    [ "#if defined(__clang__) && !defined(_MSC_VER)"
    ; "#pragma clang diagnostic push"
    ; "#pragma clang diagnostic ignored \"-Wparentheses-equality\""
    ; "#pragma clang diagnostic ignored \"-Wunused-label\""
    ; "#pragma clang diagnostic ignored \"-Wunused-value\""
    ; "#elif defined(__GNUC__)"
    ; "#pragma GCC diagnostic push"
    ; "#pragma GCC diagnostic ignored \"-Wunused-label\""
    ; "#pragma GCC diagnostic ignored \"-Wunused-value\""
    ; "#pragma GCC diagnostic ignored \"-Wunused-but-set-variable\""
    ; "#endif"
    ] ^^
  hardline

let doc_footer =
  let open PPrint in
  separate_map hardline string
    [ "#if defined(__clang__) && !defined(_MSC_VER)"
    ; "#pragma clang diagnostic pop"
    ; "#elif defined(__GNUC__)"
    ; "#pragma GCC diagnostic pop"
    ; "#endif"
    ] ^^
  hardline

(* encoder and decoder methods *)

let gen_ctyp_variant pp def =
  let open Jib in
  let open PPrint in
  let open PP_bytecode in

  match def with
  | CDEF_type (CTD_variant (id, ctors)) ->
      let tag =
        let gen_tag (id, _) = string "Kind_" ^^ pp_id id in
        let members =
          let invalid = string "Kind_" ^^ pp_id id ^^ string "_invalid" in
          invalid ^^ comma ^^ hardline ^^ separate_map (comma ^^ hardline) gen_tag ctors
        in
        string "enum kind_" ^^ pp_id id ^^ hardline ^^ pp_block members ^^ semi
      in
      let body =
        let each_ctor kid f ctors =
          let rec go = function
            | [] -> string "default: break;"
            | (ctor_id, ctyp) :: ctors ->
                string "case Kind_" ^^ pp_id ctor_id ^^ colon ^^ hardline ^^
                pp_block (f ctor_id ctyp ^^ hardline ^^ string "break;") ^^ hardline ^^
                go ctors
          in
          string "switch " ^^ parens kid ^^ hardline ^^
          pp_block (go ctors)
        in
        let def_ctor =
          pp_id id ^^ string "()" ^^ hardline ^^
          pp_block (string "this->kind = Kind_" ^^ pp_id id ^^ string "_invalid;")
        in
        let dtor =
          let gen_dtor ctor_id ctyp =
            let f = string "&this->" ^^ pp_id ctor_id in
            string "sail::destroy_at" ^^ parens f ^^ semi
          in
          let set_kind = string "this->kind = Kind_" ^^ pp_id id ^^ string "_invalid;" in
          tilde ^^ pp_id id ^^ string "()" ^^ hardline ^^
          pp_block (each_ctor (string "this->kind") gen_dtor ctors ^^ hardline ^^ set_kind)
        in
        let copy =
          let gen_set_field rhs ctor_id ctyp =
            let lhs = string "this->" ^^ pp_id ctor_id in
            let rhs = string rhs ^^ dot ^^ pp_id ctor_id in
            string "::new" ^^ parens (ampersand ^^ lhs) ^^ space ^^ pp_ctyp pp false ctyp ^^ parens rhs ^^ semi
          in
          pp_id id ^^ parens (string "const " ^^ pp_id id ^^ string " &rhs") ^^ hardline ^^
          pp_block (
            string "this->kind = rhs.kind;" ^^ hardline ^^
            each_ctor (string "rhs.kind") (gen_set_field "rhs") ctors
          )
        in
        let copy_op =
          pp_id id ^^ string " & operator=" ^^
          parens (string "const " ^^ pp_id id ^^ string " &rhs") ^^ hardline ^^
          pp_block (
            string "sail::destroy_at(this);" ^^ hardline ^^
            string "::new(this) " ^^ pp_id id ^^ parens (string "rhs") ^^ semi ^^ hardline ^^
            string "return *this;"
          )
        in
        let equal_op =
          let gen_cmp rhs ctor_id _ =
            string "return this->" ^^ pp_id ctor_id ^^ string " == " ^^
            rhs ^^ dot ^^ pp_id ctor_id ^^ semi
          in
          string "bool operator==" ^^
          parens (string "const " ^^ pp_id id ^^ string " &rhs") ^^ string " const" ^^ hardline ^^
          pp_block (
            string "if (this->kind != rhs.kind)" ^^ hardline ^^
            string "    return false;" ^^ hardline ^^
            each_ctor (string "this->kind") (gen_cmp (string "rhs")) ctors ^^ hardline ^^
            string "return false;"
          )
        in
        let gen_ctor_var (ctor_id, ctyp) = pp_ctyp pp false ctyp ^^ space ^^ pp_id ctor_id ^^ semi in
        let members = separate hardline
          [ def_ctor
          ; dtor
          ; copy
          ; copy_op
          ; equal_op
          ; string "kind_" ^^ pp_id id ^^ space ^^ string "kind" ^^ semi
          ; string "union" ^^ hardline ^^ pp_block (separate_map (hardline) gen_ctor_var ctors)
          ] ^^ semi
        in
        string "struct " ^^ pp_id id ^^ hardline ^^ pp_block members ^^ semi
      in
      let gen_ctor_fun (ctor_id, ctyp) =
        let lhs = string "rop." ^^ pp_id ctor_id in
        let rhs = string "op" in
        pp_id id ^^ space ^^ pp_id ctor_id ^^
        parens (string "const " ^^ pp_ctyp pp false ctyp ^^ string " &op") ^^ hardline ^^
        pp_block (separate (semi ^^ hardline)
          [ pp_id id ^^ space ^^ string "rop"
          ; string "rop.kind = Kind_" ^^ pp_id ctor_id
          ; string "::new" ^^ parens (ampersand ^^ lhs) ^^ space ^^ pp_ctyp pp false ctyp ^^ parens rhs
          ; string "return rop"
          ] ^^ semi
        )
      in
      tag ^^ hardline ^^ body ^^ hardline ^^ separate_map hardline gen_ctor_fun ctors
  | _ -> assert false

let identify_extimm_ctors var_id var_map =
  let is_expr s = string_match "[a-z0-9_']+_expr" (string_of_id s) in
  match Ast_util.Bindings.find_opt var_id var_map with
  | Some [(id0, typ0); (id1, typ1)] ->
      if is_expr id0 then
        ((id1, typ1), (id0, typ0))
      else if is_expr id1 then
        ((id0, typ0), (id1, typ1))
      else
        let msg = "Expected " ^ string_of_id var_id ^ " has a constructor name ends with '_expr'" in
        raise (Reporting.err_general Parse_ast.Unknown msg)
  | _ ->
      let msg = "Expected " ^ string_of_id var_id ^ " has 2 constructors" in
      raise (Reporting.err_general Parse_ast.Unknown msg)

type op_mapping_fun =
  | Op_mapping_fun of Jib.cdef
  | Entry_op_fun of string * inst_op
  | Extern_op_fun of string * inst_op
  | No_op_fun of inst_op

let gen_encoder ctx def =
  let open Jib in
  let open PPrint in
  let open PP_bytecode in

  let pp = printers_base ctx in

  let fn_name (op : inst_op) = "encode_" ^ !opt_td_prefix ^ op.name ^ "_op" in
  let proto ns =
    match def with
    | Op_mapping_fun (CDEF_fundef (id, _, [arg], _)) ->
        let (arg_ctyp, ret_ctyp) =
          let ([arg_typ], ret_typ) = get_fundef_typ ctx id in
          (ctyp_of_typ ctx arg_typ, ctyp_of_typ ctx ret_typ)
        in
        let arg_ty = pp_ctyp pp ns arg_ctyp in
        let arg_decl = string "const " ^^ arg_ty ^^ string " &" ^^ pp_id arg in
        let ret_ty = pp_ctyp pp ns ret_ctyp in
        let fn = cpp_class_id ns (pp_id id) in
        ret_ty ^^ space ^^ fn ^^ parens arg_decl ^^ string " const"
    | Entry_op_fun (_, op)
    | Extern_op_fun (_, op)
    | No_op_fun op ->
        let fn = cpp_class_id ns (string (fn_name op)) in
        string "unsigned " ^^ fn ^^ string ("(const llvm::MCInst &MI, unsigned OpIdx, " ^
          "llvm::SmallVectorImpl<llvm::MCFixup> &Fixups, const llvm::MCSubtargetInfo &STI) const"
        )
  in

  let decl_doc = proto false ^^ semi in
  let impl_doc_body =
    match def with
    | Op_mapping_fun def -> (
        match def with
        | CDEF_fundef (_, _, _, instrs) -> separate_map hardline (pp_instr pp) instrs
        | _ -> assert false
      )
    | Entry_op_fun (fun_name, _) ->
        let open Ast_util in

        let id = mk_id fun_name in
        let (arg_ctyp, ret_ctyp) =
          let ([arg_typ], ret_typ) = get_fundef_typ ctx id in
          (ctyp_of_typ ctx arg_typ, ctyp_of_typ ctx ret_typ)
        in

        let arg = string "sail_arg" in
        let match_fun = pp_id (mk_id (fun_name ^ "_matches")) ^^ parens arg in
        let arg_conv = parens (pp_ctyp pp false arg_ctyp) in

        let decl = pp_ctyp pp false arg_ctyp ^^ space ^^ arg ^^ semi in
        let init =
          if is_extimm_ctyp arg_ctyp then
            let CT_variant (var_id, _) = arg_ctyp in
            let ((imm_id, imm_ctyp), (expr_id, expr_ctyp)) = identify_extimm_ctors var_id ctx.var_ctor_map in

            let imm_conv = parens (pp_ctyp pp false imm_ctyp) in
            let expr_conv = parens (pp_ctyp pp false expr_ctyp) in

            string "if (MI.getOperand(OpIdx).isImm())" ^^ hardline ^^
            string "    " ^^ arg ^^ string " = " ^^ pp_id imm_id ^^
            parens (imm_conv ^^ string "MI.getOperand(OpIdx).getImm()") ^^ semi ^^ hardline ^^

            string "else if (MI.getOperand(OpIdx).isExpr())" ^^ hardline ^^
            string "    " ^^ arg ^^ string " = " ^^ pp_id expr_id ^^
            parens (expr_conv ^^ string "MI.getOperand(OpIdx).getExpr()") ^^ semi ^^ hardline ^^

            string "else" ^^ hardline ^^
            string "    llvm_unreachable(\"match failure\");"
          else if is_regid_ctyp arg_ctyp then
            arg ^^ string " = " ^^ arg_conv ^^ string "MI.getOperand(OpIdx).getReg();"
          else
            arg ^^ string " = " ^^ arg_conv ^^ string "MI.getOperand(OpIdx).getImm();"
        in

        decl ^^ hardline ^^ init ^^ hardline ^^
        string "if (!" ^^ match_fun ^^ string ")" ^^ hardline ^^
        string "    llvm_unreachable(\"match failure\");" ^^ hardline ^^
        string "return (unsigned)" ^^ pp_id id ^^ parens arg ^^ semi
    | Extern_op_fun (fun_name, _) ->
        string ("return " ^ fun_name ^ "(MI, OpIdx, Fixups, STI)") ^^ semi
    | No_op_fun op ->
        let bits = string_of_int op.bit_size in
        match op.subops with
        | No_subops ->
            string ("return encodeUImm<" ^ bits ^ ">(MI, OpIdx, Fixups, STI)") ^^ semi
        | Field_concat fs ->
            let gen_check_val doc (bf, (lo, _)) =
              let lit_size =
                match bf with
                | Bin_str b -> Some ("0b" ^ b, String.length b)
                | Hex_str b -> Some ("0x" ^ b, String.length b * 4)
                | _ -> None
              in
              Option.map_default (fun (lit, size) ->
                let stmt =
                  let start = string_of_int lo in
                  let mask = string_of_int size in
                  "unsigned Tmp = (Value >> " ^ start ^ ") & (((unsigned)1 << " ^ mask ^ ") - 1);"
                in
                let stmts = separate_map hardline string
                  [ stmt
                  ; "if (Tmp != ((unsigned)" ^ lit ^ "))"
                  ; "    report_fatal_error(\"invalid immediate\");"
                  ]
                in
                doc ^^ pp_block stmts ^^ (if lo = 0 then empty else hardline)
              ) doc lit_size
            in
            let init = string "unsigned Value = MI.getOperand(OpIdx).getImm()" ^^ semi in
            let stmts = List.fold_left gen_check_val empty fs in
            let ret = string ("return encodeUImm<" ^ bits ^ ">(MI, OpIdx, Fixups, STI)") ^^ semi in
            init ^^ hardline ^^ stmts ^^ hardline ^^ ret
        | Op_tuple subops ->
            let gen_subop (doc, idx, hi) (op : inst_op) =
              let lo = hi - op.bit_size + 1 in
              let stmts = separate_map hardline string
                [ "unsigned Tmp = " ^ fn_name op ^ "(MI, OpIdx + " ^ string_of_int idx ^ ", Fixups, STI);"
                ; "Value |= Tmp << " ^ string_of_int lo ^ ";"
                ]
              in
              (doc ^^ pp_block stmts ^^ (if lo = 0 then empty else hardline), idx + 1, lo - 1)
            in
            let init = string "unsigned Value = 0" ^^ semi in
            let (doc, _, _) = List.fold_left gen_subop (empty, 0, op.bit_size - 1) subops in
            let ret = string "return Value" ^^ semi in
            init ^^ hardline ^^ doc ^^ hardline ^^ ret
  in
  let impl_doc = proto true ^^ hardline ^^ pp_block impl_doc_body in
  (decl_doc, impl_doc)

let gen_decoder ctx def =
  let open Jib in
  let open PPrint in
  let open PP_bytecode in

  let pp = printers_base ctx in

  let fn_name (op : inst_op) = "decode_" ^ !opt_td_prefix ^ op.name ^ "_op" in
  let proto ns =
    match def with
    | Op_mapping_fun (CDEF_fundef (id, _, [arg], _)) ->
        let (arg_ctyp, ret_ctyp) =
          let ([arg_typ], ret_typ) = get_fundef_typ ctx id in
          (ctyp_of_typ ctx arg_typ, ctyp_of_typ ctx ret_typ)
        in
        let arg_ty = pp_ctyp pp ns arg_ctyp in
        let arg_decl = string "const " ^^ arg_ty ^^ string " &" ^^ pp_id arg in
        let ret_ty = pp_ctyp pp ns ret_ctyp in
        let fn = cpp_class_id ns (pp_id id) in
        string "static " ^^ ret_ty ^^ space ^^ fn ^^ parens arg_decl
    | Entry_op_fun (_, op)
    | Extern_op_fun (_, op)
    | No_op_fun op ->
        let fn = cpp_class_id ns (string (fn_name op)) in
        string "static llvm::MCDisassembler::DecodeStatus " ^^ fn ^^
        string "(llvm::MCInst &MI, unsigned Field, uint64_t Address, const void *Decoder)"
  in

  let decl_doc = proto false ^^ semi in
  let impl_doc_body =
    match def with
    | Op_mapping_fun def ->
      (
        match def with
        | CDEF_fundef (_, _, _, instrs) -> separate_map hardline (pp_instr pp) instrs
        | _ -> assert false
      )
    | Entry_op_fun (fun_name, _) ->
        let open Ast_util in

        let id = mk_id fun_name in
        let (arg_ctyp, ret_ctyp) =
          let ([arg_typ], ret_typ) = get_fundef_typ ctx id in
          (ctyp_of_typ ctx arg_typ, ctyp_of_typ ctx ret_typ)
        in

        let ret = string "sail_ret" in
        let arg = parens (pp_ctyp pp false arg_ctyp) ^^ string "Field" in
        let match_fun = pp_id (mk_id (fun_name ^ "_matches")) ^^ parens arg in

        let init =
          pp_ctyp pp false ret_ctyp ^^ space ^^ ret ^^ string " = " ^^
          pp_id id ^^ parens arg ^^ semi
        in
        let conv =
          if is_extimm_ctyp ret_ctyp then
            let CT_variant (var_id, _) = ret_ctyp in
            let ((imm_id, _), (expr_id, _)) = identify_extimm_ctors var_id ctx.var_ctor_map in

            separate hardline
              [ string "if " ^^ parens (ret ^^ dot ^^ string "kind == Kind_" ^^ pp_id imm_id)
              ; string "    MI.addOperand(llvm::MCOperand::createImm((std::int64_t)" ^^
                ret ^^ dot ^^ pp_id imm_id ^^ string "));"
              ; string "else if " ^^ parens (ret ^^ dot ^^ string "kind == Kind_" ^^ pp_id expr_id)
              ; string "    MI.addOperand(llvm::MCOperand::createExpr((llvm::MCExpr *)" ^^
                ret ^^ dot ^^ pp_id expr_id ^^ string "));"
              ; string "else"
              ; string "    return llvm::MCDisassembler::Fail;"
              ]
          else if is_regid_ctyp ret_ctyp then
            string "MI.addOperand(llvm::MCOperand::createReg((unsigned)" ^^ ret ^^ string "));"
          else
            string "MI.addOperand(llvm::MCOperand::createImm((std::int64_t)" ^^ ret ^^ string "));"
        in

        separate hardline
          [ string "if (!" ^^ match_fun ^^ string ")"
          ; string "    return llvm::MCDisassembler::Fail;"
          ; init ^^ hardline ^^ conv
          ; string "return llvm::MCDisassembler::Success;"
          ]
    | Extern_op_fun (fun_name, _) ->
        string ("return " ^ fun_name ^ "(MI, Field, Address, Decoder)") ^^ semi
    | No_op_fun op ->
        match op.subops with
        | No_subops ->
            let mcop = string "llvm::MCOperand::createImm((std::int64_t)Field)" in
            string "MI.addOperand" ^^ parens mcop ^^ semi ^^ hardline ^^
            string "return llvm::MCDisassembler::Success" ^^ semi
        | Field_concat fs ->
            let gen_set_val doc (bf, (lo, _)) =
              let lit =
                match bf with
                | Bin_str b -> Some ("0b" ^ b)
                | Hex_str b -> Some ("0x" ^ b)
                | _ -> None
              in
              Option.map_default (fun lit ->
                let stmt =
                  let start = string_of_int lo in
                  "Field |= ((unsigned)0b" ^ lit ^ ") << " ^ start ^ ";"
                in
                doc ^^ string stmt ^^ hardline
              ) doc lit
            in
            let stmts = List.fold_left gen_set_val empty fs in
            let mcop = string "llvm::MCOperand::createImm((std::int64_t)Field)" in
            string "MI.addOperand" ^^ parens mcop ^^ semi ^^ hardline ^^
            string "return llvm::MCDisassembler::Success" ^^ semi
        | Op_tuple subops ->
            let gen_subop (doc, hi) (op : inst_op) =
              let lo = hi - op.bit_size + 1 in
              let stmt =
                let start = string_of_int lo in
                let mask = string_of_int op.bit_size in
                "unsigned Tmp = (Field >> " ^ start ^ ") & (((unsigned)1 << " ^ mask ^ ") - 1);"
              in
              let stmts = separate_map hardline string
                [ stmt
                ; "if (" ^ fn_name op ^ "(MI, Tmp, Address, Decoder) != llvm::MCDisassembler::Success)"
                ; "    return llvm::MCDisassembler::Fail;"
                ]
              in
              (doc ^^ pp_block stmts ^^ (if lo = 0 then empty else hardline), lo - 1)
            in
            let (doc, _) = List.fold_left gen_subop (empty, op.bit_size - 1) subops in
            doc
  in
  let impl_doc = proto true ^^ hardline ^^ pp_block impl_doc_body in
  (decl_doc, impl_doc)

let compile_op_mappings is_encoder ctx ast =
  let open Ast_util in
  let open PPrint in

  let cpu = get_cpu_def ctx ast in
  let ctx = collect_fun_typ_ids ctx ast in

  let mapping_fun_name fwd name = name ^ (if fwd then "_forwards" else "_backwards") in
  let op_fun_name = mapping_fun_name (not is_encoder) in

  let entry_funs = List.fold_left (fun ids op ->
      if String.length op.mapping = 0 then
        ids
      else
        let f = op_fun_name op.mapping in
        let fid = mk_id f in
        let ids = IdSet.add fid ids in
        if TC.Env.is_extern fid ctx.tc_env "llvm" then
          ids
        else
          IdSet.add (mk_id (f ^ "_matches")) ids
    ) IdSet.empty cpu.ops
  in
  let (cdefs, ctx) = compile_ast ctx ast entry_funs in

  let codegen_fun = if is_encoder then gen_encoder else gen_decoder in
  let cpp_guard is_decl doc =
    let guard =
      let fn = if is_encoder then "ENCODER" else "DECODER" in
      let ty = if is_decl then "DECLS" else "IMPLS" in
      "GET_" ^ fn ^ "_METHOD_" ^ ty
    in
    separate hardline
      [ string ("#ifdef " ^ guard)
      ; string ("#undef " ^ guard)
      ; separate hardline doc
      ; string ("#endif // " ^ guard)
      ] ^^
    hardline
  in

  let (fundefs, fundef_lst) =
    let open Jib in
    List.fold_left (fun (map, lst) def ->
      match def with
      | CDEF_fundef (id, _, _, _) when IdSet.mem id ctx.used_funs ->
          let map = StringMap.add (string_of_id id) def map in
          let lst = def :: lst in
          (map, lst)
      | _ -> (map, lst)
    ) (StringMap.empty, []) cdefs
  in

  let decl_docs = List.fold_left (fun docs cdef ->
      let open Jib in
      let open PP_bytecode in
      match cdef with
      | CDEF_type (CTD_variant (id, _)) when IdSet.mem id ctx.used_ctyps ->
          let doc = gen_ctyp_variant (printers_base ctx) cdef in
          doc :: docs
      | _ -> docs
    ) [] cdefs
  in

  let (decl_docs, impl_docs) = (decl_docs, []) in

  let codegen (decl_docs, impl_docs) def =
    let (decl_doc, impl_doc) = codegen_fun ctx (Op_mapping_fun def) in
    (decl_doc :: decl_docs, impl_doc :: impl_docs)
  in
  let (decl_docs, impl_docs) = List.fold_left codegen (decl_docs, impl_docs) (List.rev fundef_lst) in

  let codegen (decl_docs, impl_docs) op =
    let def =
      if String.length op.mapping = 0 then
        No_op_fun op
      else
        let fun_name = op_fun_name op.mapping in
        match StringMap.find_opt fun_name fundefs with
        | Some _ -> Entry_op_fun (fun_name, op)
        | None ->
            let fun_id = mk_id fun_name in
            if TC.Env.is_extern fun_id ctx.tc_env "llvm" then
              Extern_op_fun (TC.Env.get_extern fun_id ctx.tc_env "llvm", op)
            else
              let msg = "Failed to find mapping function: " ^ fun_name in
              raise (Reporting.err_general Parse_ast.Unknown msg)
    in
    let (decl_doc, impl_doc) = codegen_fun ctx def in
    (decl_doc :: decl_docs, impl_doc :: impl_docs)
  in

  let (decl_docs, impl_docs) = List.fold_left codegen (decl_docs, impl_docs) cpu.ops in
  doc_header ^^
  cpp_guard true (List.rev decl_docs) ^^
  cpp_guard false (List.rev impl_docs) ^^
  doc_footer

let output_encoder_methods out ctx ast =
  let doc = compile_op_mappings true ctx ast in
  pp_doc out doc

let output_decoder_methods out ctx ast =
  let doc = compile_op_mappings false ctx ast in
  pp_doc out doc

(* parser and printer methods *)

let gen_mcinst_of_ast ctx =
  let open Ast_util in
  let open PPrint in
  let open PP_bytecode in

  let codegen ast_typ (decl_docs, impl_docs) =
    match Bindings.find_opt ast_typ ctx.var_ctor_map with
    | Some ctors ->
        let pp = printers_base ctx in

        let proto ns =
          let fname = "convert_mcinst_of_" ^ string_of_id ast_typ in
          let fname = cpp_class_id ns (string fname) in
          let ret_ty = string "llvm::Optional<llvm::MCInst>" in
          let arg_ty = cpp_class_id ns (pp_id ast_typ) in
          ret_ty ^^ space ^^ fname ^^ parens (string "const " ^^ arg_ty ^^ string " &ast")
        in

        let each_ctor obj f ctors =
          let rec go = function
            | [] -> string "default: return llvm::None;"
            | (ctor_id, ctyp) :: ctors ->
                string "case Kind_" ^^ pp_id ctor_id ^^ colon ^^ hardline ^^
                pp_block (f obj ctor_id ctyp ^^ hardline ^^ string "break;") ^^ hardline ^^
                go ctors
          in
          string "switch " ^^ parens (obj ^^ dot ^^ string "kind") ^^ hardline ^^
          pp_block (go ctors)
        in
        let add_op ty obj =
          string "inst.addOperand" ^^
          parens (string "llvm::MCOperand::create" ^^ string ty ^^ parens obj) ^^ semi
        in
        let add_extimm_op var_id obj =
          let ((imm_id, _), (expr_id, _)) = identify_extimm_ctors var_id ctx.var_ctor_map in
          let cond id = obj ^^ dot ^^ string "kind == Kind_" ^^ pp_id id in
          string "if " ^^ parens (cond imm_id) ^^ hardline ^^
          pp_block (add_op "Imm" (string "(std::int64_t)" ^^ obj ^^ dot ^^ pp_id imm_id)) ^^ hardline ^^
          string "else if " ^^ parens (cond expr_id) ^^ hardline ^^
          pp_block (add_op "Expr" (string "(llvm::MCExpr *)" ^^ obj ^^ dot ^^ pp_id expr_id)) ^^ hardline ^^
          string "else" ^^ hardline ^^
          pp_block (string "return llvm::None;")
        in
        let rec add_ctor_ops obj ctor_id ctyp =
          let open Jib in

          let field =
            match get_tuple_field (string_of_id ctor_id) with
            | Some n -> string "std::get" ^^ angles (string n) ^^ parens obj
            | None -> obj ^^ dot ^^ pp_id ctor_id
          in
          match ctyp with
          | CT_bit
          | CT_lbits _
          | CT_sbits _
          | CT_fbits _
          | CT_lint
          | CT_fint _ ->
              add_op "Imm" field
          | CT_enum _ ->
              add_op (if is_regid_ctyp ctyp then "Reg" else "Imm") field
          | CT_tup elems ->
              let add_elems ix = add_ctor_ops field (mk_id ("ztup" ^ string_of_int ix)) in
              separate hardline (List.mapi add_elems elems)
          | CT_variant (var_id, ctors) ->
              if is_extimm_typ var_id then
                add_extimm_op var_id field
              else
                each_ctor field add_ctor_ops ctors
          | CT_unit -> empty
          | _ -> assert false
        in

        let gen_impl obj ctors =
          let set_inst obj ctor_id ctyp =
            let opcode = !opt_td_prefix ^ string_of_id ctor_id in
            let opcode = cpp_id (string opcode) in
            string "inst.setOpcode" ^^ parens opcode ^^ semi ^^ hardline ^^
            add_ctor_ops obj ctor_id ctyp
          in
          each_ctor obj set_inst ctors
        in

        let decl_doc = proto false ^^ semi in
        let impl_doc =
          let init = string "llvm::MCInst inst;" in
          let fini = string "return inst;" in
          let impl_body = gen_impl (string "ast") ctors in
          let impl_body = init ^^ hardline ^^ impl_body ^^ hardline ^^ fini in
          proto true ^^ hardline ^^ pp_block impl_body
        in
        (decl_doc :: decl_docs, impl_doc :: impl_docs)
    | None ->
        let msg = "Failed to find variant: " ^ string_of_id ast_typ in
        raise (Reporting.err_general Parse_ast.Unknown msg)
  in
  IdSet.fold codegen ctx.ast_typs ([], [])

let gen_parser ctx def =
  let open Jib in
  let open PPrint in
  let open PP_bytecode in

  let gen_ctyp pp ns ctyp =
    match ctyp with
    | CT_string -> string "sail::TokenString"
    | _ -> (printers_base ctx).pp_ctyp pp ns ctyp
  in

  match def with
  | CDEF_fundef (id, ret_opt, [arg], instrs) ->
      let (arg_ctyp, ret_ctyp) =
        let ([arg_typ], ret_typ) = get_fundef_typ ctx id in
        (ctyp_of_typ ctx arg_typ, ctyp_of_typ ctx ret_typ)
      in
      let is_ret_ast = is_ast_ctyp ret_ctyp in

      let gen_instr pp (I_aux (instr, _) as cinstr) =
        match instr with
        | I_match_failure ->
            string (
              if is_ret_ast then
                "return llvm::None;"
              else
                "llvm_unreachable(\"match_failure\");"
            )
        | _ ->
            (printers_base ctx).pp_instr pp cinstr
      in
      let pp =
        let pp = printers_base ctx in
        { pp with
          pp_instr = gen_instr
        ; pp_ctyp = gen_ctyp
        }
      in

      let proto ns =
        let arg_ty = pp_ctyp pp ns arg_ctyp in
        let arg_decl = string "const " ^^ arg_ty ^^ string " &" ^^ pp_id arg in
        let ret_ty =
          let t = pp_ctyp pp ns ret_ctyp in
          if is_ret_ast then string "llvm::Optional" ^^ angles t else t
        in
        let fn = cpp_class_id ns (pp_id id) in
        ret_ty ^^ space ^^ fn ^^ parens arg_decl
      in

      let decl_doc = proto false ^^ semi in
      let impl_doc_body =
        let body = separate hardline (List.map (pp_instr pp) instrs) in
        match ret_opt with
        | Some ret_id ->
            let init = separate (semi ^^ hardline)
              [ separate space [pp_ctyp pp false ret_ctyp; string "ret_var"]
              ; separate space [pp_ctyp pp false ret_ctyp; star ^^ pp_id ret_id; equals; string "&ret_var"]
              ] ^^ semi
            in
            let fini = string "return ret_var" ^^ semi in
            init ^^ hardline ^^ body ^^ hardline ^^ fini
        | None -> body
      in
      let impl_doc = proto true ^^ hardline ^^ pp_block impl_doc_body in
      (decl_doc, impl_doc)
  | CDEF_type (CTD_variant (_, _)) ->
      let pp =
        let pp = printers_base ctx in
        { pp with
          pp_ctyp = gen_ctyp
        }
      in
      let decl_doc = gen_ctyp_variant pp def in
      (decl_doc, empty)
  | _ -> assert false

let gen_ast_of_mcinst ctx =
  let open Ast_util in
  let open PPrint in
  let open PP_bytecode in

  let codegen ast_typ (decl_docs, impl_docs) =
    match Bindings.find_opt ast_typ ctx.var_ctor_map with
    | Some ctors ->
        let pp = printers_base ctx in

        let proto ns =
          let fname = "convert_" ^ string_of_id ast_typ ^ "_of_mcinst" in
          let fname = cpp_class_id ns (string fname) in
          let arg_ty = cpp_class_id ns (pp_id ast_typ) in
          string "llvm::Optional" ^^ angles arg_ty ^^ space ^^ fname ^^ parens (string "const llvm::MCInst &inst")
        in

        let ast_op_id = ref 0 in
        let reset_ast_op_id () = ast_op_id := 0 in
        let next_ast_op_id () =
          let id = !ast_op_id in
          ast_op_id := !ast_op_id + 1;
          id
        in

        let inst_op_ix = ref 0 in
        let reset_inst_op_ix () = inst_op_ix := 0 in
        let next_inst_op_ix () =
          let ix = !inst_op_ix in
          inst_op_ix := !inst_op_ix + 1;
          ix
        in

        let each_ctor kid_opt f ctors =
          match kid_opt with
          | Some kid ->
              let rec go = function
                | [] -> string "default: return llvm::None;"
                | (ctor_id, ctyp) :: ctors ->
                    let opcode = !opt_td_prefix ^ string_of_id ctor_id in
                    let opcode = cpp_id (string opcode) in
                    string "case " ^^ opcode ^^ colon ^^ hardline ^^
                    pp_block (f ctor_id ctyp ^^ hardline ^^ string "break;") ^^ hardline ^^
                    go ctors
              in
              string "switch " ^^ parens kid ^^ hardline ^^
              pp_block (go ctors)
          | None ->
              let rec go = function
                | [] -> assert false
                | [(ctor_id, ctyp)] ->
                    pp_block (f ctor_id ctyp)
                | (ctor_id, ctyp) :: ctors ->
                    pp_block (f ctor_id ctyp) ^^ hardline ^^
                    go ctors
              in
              go ctors
        in
        let get_op_val ty op_ix =
          let inst_op = string "inst.getOperand" ^^ parens (string (string_of_int op_ix)) in
          inst_op ^^ string (".get" ^ ty ^ "()")
        in
        let set_extimm_op var_id obj op_ix =
          let ((imm_id, imm_ctyp), (expr_id, expr_ctyp)) = identify_extimm_ctors var_id ctx.var_ctor_map in
          let imm_conv = parens (pp_ctyp pp false imm_ctyp) in
          let expr_conv = parens (pp_ctyp pp false expr_ctyp) in

          let inst_op = string "inst.getOperand" ^^ parens (string (string_of_int op_ix)) in
          let cond ty = inst_op ^^ string (".is" ^ ty ^ "()") in
          let set_obj ty id conv = obj ^^ string " = " ^^ pp_id id ^^ parens (
              conv ^^ get_op_val ty op_ix
            ) ^^ semi
          in
          string "if " ^^ parens (cond "Imm") ^^ hardline ^^
          pp_block (set_obj "Imm" imm_id imm_conv) ^^ hardline ^^
          string "else if " ^^ parens (cond "Expr") ^^ hardline ^^
          pp_block (set_obj "Expr" expr_id expr_conv) ^^ hardline ^^
          string "else" ^^ hardline ^^
          pp_block (string "return llvm::None;")
        in
        let rec set_ctor_ops obj ctor_id ctyp =
          let open Jib in

          let set_obj op_val =
            let op_val =
              match ctyp with
              | CT_tup _ -> string "std::make_tuple" ^^ parens op_val
              | CT_variant _ -> pp_id ctor_id ^^ parens op_val
              | _ -> op_val
            in
            obj ^^ string " = " ^^ op_val ^^ semi
          in
          match ctyp with
          | CT_bit
          | CT_lbits _
          | CT_sbits _
          | CT_fbits _
          | CT_lint
          | CT_fint _ ->
              let inst_op_ix = next_inst_op_ix () in
              let op_val = get_op_val "Imm" inst_op_ix in
              set_obj op_val
          | CT_enum _ ->
              let inst_op_ix = next_inst_op_ix () in
              let ty = if is_regid_ctyp ctyp then "Reg" else "Imm" in
              let op_val = get_op_val ty inst_op_ix in
              set_obj op_val
          | CT_tup elems ->
              let tup_objs = List.map (fun _ -> string ("op" ^ string_of_int (next_ast_op_id ()))) elems in
              let set_tup_objs = List.map2 (fun obj ctyp ->
                  pp_ctyp pp false ctyp ^^ space ^^ obj ^^ semi ^^ hardline ^^
                  set_ctor_ops obj (mk_id "") ctyp
                ) tup_objs elems
              in
              pp_block (
                separate hardline set_tup_objs ^^ hardline ^^
                set_obj (separate (comma ^^ space) tup_objs)
              )
          | CT_variant (var_id, ctors) ->
              if is_extimm_typ var_id then
                let inst_op_ix = next_inst_op_ix () in
                set_extimm_op var_id obj inst_op_ix
              else
                let set_op ctor_id ctyp =
                  let var_op = string ("op" ^ string_of_int (next_ast_op_id ())) in
                  let init = pp_ctyp pp false ctyp ^^ space ^^ var_op ^^ semi in
                  let fini = obj ^^ string " = " ^^ pp_id ctor_id ^^ parens var_op ^^ semi in
                  let inner = set_ctor_ops var_op (mk_id "") ctyp in
                  init ^^ hardline ^^ inner ^^ hardline ^^ fini
                in
                each_ctor None set_op ctors
          | CT_unit -> empty
          | _ -> assert false
        in

        let rec get_num_ops n ctyp =
          let open Jib in
          match ctyp with
          | CT_bit
          | CT_lbits _
          | CT_sbits _
          | CT_fbits _
          | CT_lint
          | CT_fint _
          | CT_enum _ -> n + 1
          | CT_tup elems ->
              List.fold_left get_num_ops n elems
          | CT_variant (var_id, ctors) ->
              if is_extimm_typ var_id then
                n + 1
              else
                List.fold_left get_num_ops n (List.map (fun (_, ctyp) -> ctyp) ctors)
          | CT_unit -> n
          | _ -> assert false
        in

        let gen_impl ctors =
          let set_inst obj ctor_id ctyp =
            reset_ast_op_id ();
            reset_inst_op_ix ();
            let var_op = string ("op" ^ string_of_int (next_ast_op_id ())) in
            let init = pp_ctyp pp false ctyp ^^ space ^^ var_op ^^ semi in
            let fini = obj ^^ string " = " ^^ pp_id ctor_id ^^ parens var_op ^^ semi in
            let inner = set_ctor_ops var_op (mk_id "") ctyp in
            let cond = string "if " ^^ parens (string ("inst.getNumOperands() == " ^ string_of_int (get_num_ops 0 ctyp))) in
            cond ^^ hardline ^^ pp_block (init ^^ hardline ^^ inner ^^ hardline ^^ fini)
          in
          each_ctor (Some (string "inst.getOpcode()")) (set_inst (string "ast")) ctors
        in

        let decl_doc = proto false ^^ semi in
        let impl_doc =
          let init = pp_id ast_typ ^^ string " ast;" in
          let fini = string "return ast;" in
          let impl_body = gen_impl ctors in
          let impl_body = init ^^ hardline ^^ impl_body ^^ hardline ^^ fini in
          proto true ^^ hardline ^^ pp_block impl_body
        in
        (decl_doc :: decl_docs, impl_doc :: impl_docs)
    | None ->
        let msg = "Failed to find variant: " ^ string_of_id ast_typ in
        raise (Reporting.err_general Parse_ast.Unknown msg)
  in
  IdSet.fold codegen ctx.ast_typs ([], [])

let gen_printer ctx def =
  let open Jib in
  let open PPrint in
  let open PP_bytecode in

  match def with
  | CDEF_fundef (id, ret_opt, [arg], instrs) ->
      let pp = printers_base ctx in

      let (arg_ctyp, ret_ctyp) =
        let ([arg_typ], ret_typ) = get_fundef_typ ctx id in
        (ctyp_of_typ ctx arg_typ, ctyp_of_typ ctx ret_typ)
      in

      let proto ns =
        let arg_ty = pp_ctyp pp ns arg_ctyp in
        let arg_decl = string "const " ^^ arg_ty ^^ string " &" ^^ pp_id arg in
        let ret_ty = pp_ctyp pp ns ret_ctyp in
        let fn = cpp_class_id ns (pp_id id) in
        ret_ty ^^ space ^^ fn ^^ parens arg_decl
      in

      let decl_doc = proto false ^^ semi in
      let impl_doc_body =
        let body = separate hardline (List.map (pp_instr pp) instrs) in
        match ret_opt with
        | Some ret_id ->
            let init = separate (semi ^^ hardline)
              [ separate space [pp_ctyp pp false ret_ctyp; string "ret_var"]
              ; separate space [pp_ctyp pp false ret_ctyp; star ^^ pp_id ret_id; equals; string "&ret_var"]
              ] ^^ semi
            in
            let fini = string "return ret_var" ^^ semi in
            init ^^ hardline ^^ body ^^ hardline ^^ fini
        | None -> body
      in
      let impl_doc = proto true ^^ hardline ^^ pp_block impl_doc_body in
      (decl_doc, impl_doc)
  | CDEF_type (CTD_variant (_, _)) ->
      let pp = printers_base ctx in
      let decl_doc = gen_ctyp_variant pp def in
      (decl_doc, empty)
  | _ -> assert false

let compile_parser_printer is_parser ctx ast =
  let open Ast_util in
  let open Jib in
  let open PPrint in

  let ctx = collect_fun_typ_ids ctx ast in

  let inst_fun_name n = n ^ (if is_parser then "_backwards" else "_forwards") in
  let entry_funs = IdSet.map (fun id -> string_of_id id |> inst_fun_name |> mk_id) ctx.asm_mapping_funs in
  let (cdefs, ctx) = compile_ast ctx ast entry_funs in

  let codegen_fun = if is_parser then gen_parser else gen_printer in
  let conv_fun = if is_parser then gen_mcinst_of_ast else gen_ast_of_mcinst in
  let cpp_guard is_decl doc =
    let guard =
      let fn = if is_parser then "PARSER" else "PRINTER" in
      let ty = if is_decl then "DECLS" else "IMPLS" in
      "GET_" ^ fn ^ "_METHOD_" ^ ty
    in
    separate hardline
      [ string ("#ifdef " ^ guard)
      ; string ("#undef " ^ guard)
      ; separate hardline doc
      ; string ("#endif // " ^ guard)
      ] ^^
    hardline
  in

  let codegen (decl_docs, impl_docs) def =
    match def with
    | CDEF_fundef (id, _, _, _) when IdSet.mem id ctx.used_funs ->
        let (decl_doc, impl_doc) = codegen_fun ctx def in
        (decl_doc :: decl_docs, impl_doc :: impl_docs)
    | CDEF_type (CTD_variant (id, _)) when IdSet.mem id ctx.used_ctyps ->
        let (decl_doc, _) = codegen_fun ctx def in
        (decl_doc :: decl_docs, impl_docs)
    | _ ->
        (decl_docs, impl_docs)
  in

  let (decl_docs, impl_docs) = List.fold_left codegen ([], []) cdefs in
  let (decl_docs, impl_docs) =
    let (conv_decl, conv_impl) = conv_fun ctx in
    (List.append conv_decl decl_docs, List.append conv_impl impl_docs)
  in
  doc_header ^^
  cpp_guard true (List.rev decl_docs) ^^
  cpp_guard false (List.rev impl_docs) ^^
  doc_footer

let output_parser_methods out ctx ast =
  let doc = compile_parser_printer true ctx ast in
  pp_doc out doc

let output_printer_methods out ctx ast =
  let doc = compile_parser_printer false ctx ast in
  pp_doc out doc
