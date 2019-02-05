val opt_inst_mapping_fun : string ref
val opt_inst_info_fun : string ref
val opt_td_inst_base : string ref
val opt_td_prefix : string ref
val opt_class_name : string ref
val opt_namespace : string ref
val opt_asm_mapping_fun : string ref
val opt_ast_typ : string ref
val opt_regid_typ : string ref
val opt_extimm_typ : string ref

type ctx

val initial_ctx : Type_check.Env.t -> ctx

val output_instrinfo_td : string option -> ctx -> Type_check.tannot Ast.defs -> unit

val output_operands_td : string option -> ctx -> Type_check.tannot Ast.defs -> unit

val output_encoder_methods : string option -> ctx -> Type_check.tannot Ast.defs -> unit

val output_decoder_methods : string option -> ctx -> Type_check.tannot Ast.defs -> unit

val output_parser_methods : string option -> ctx -> Type_check.tannot Ast.defs -> unit

val output_printer_methods : string option -> ctx -> Type_check.tannot Ast.defs -> unit
