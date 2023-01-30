include struct  end
include struct  end
include
  (Metapp_preutils :
    module type of struct include Metapp_preutils end with module Exp :=
      Metapp_preutils.Exp and module Typ := Metapp_preutils.Typ and
      module Mod := Metapp_preutils.Mod and module Mty := Metapp_preutils.Mty)
let ppxlib_version = (0, 27, 0)
let ast_version = (4, 14)
[@@@ocaml.text " {1 String constant destructor} "]
type string_constant = {
  s: string ;
  loc: Location.t ;
  delim: string option }
[@@@ocaml.text " More general reimplementation without magic "]
let destruct_string_constant (constant : Ppxlib.constant) =
  (match constant with
   | Pconst_string (s, loc, delim) -> Some { s; loc; delim }
   | _ -> None : string_constant option)
let string_of_expression (expression : Ppxlib.expression) =
  ((Ast_helper.with_default_loc expression.pexp_loc) @@
     (fun () ->
        match match expression.pexp_desc with
              | Pexp_constant constant -> destruct_string_constant constant
              | _ -> None
        with
        | Some value -> value
        | _ ->
            Location.raise_errorf ~loc:(!Ast_helper.default_loc)
              "String value expected") : string_constant)
let string_of_arbitrary_expression (expression : Ppxlib.expression) =
  ((Ast_helper.with_default_loc expression.pexp_loc) @@
     (fun () ->
        match match expression.pexp_desc with
              | Pexp_constant constant -> destruct_string_constant constant
              | _ -> None
        with
        | Some value -> value.s
        | _ -> Format.asprintf "%a" Ppxlib.Pprintast.expression expression) : 
  string)
[@@@ocaml.text " {1 Open} "]
module Opn = struct type 'a t = 'a Ppxlib.open_infos end
[@@@ocaml.text " {1 General purpose functions} "]
let rec extract_first (p : 'a -> 'b option) (l : 'a list) =
  (match l with
   | [] -> None
   | hd::tl ->
       (match p hd with
        | Some b -> Some (b, tl)
        | None ->
            (match extract_first p tl with
             | Some (b, tl) -> Some (b, (hd :: tl))
             | None -> None)) : ('b * 'a list) option)
type 'a comparer = 'a -> 'a -> int
let compare_pair compare_fst compare_snd (a, b) (c, d) =
  (let o = compare_fst a c in if o = 0 then compare_snd b d else o : 
  int)
let rec compare_list compare_item a b =
  match (a, b) with
  | ([], []) -> 0
  | (a_hd::a_tl, b_hd::b_tl) ->
      compare_pair compare_item (compare_list compare_item) (a_hd, a_tl)
        (b_hd, b_tl)
  | ([], _::_) -> (-1)
  | (_::_, []) -> 1
[@@@ocaml.text " {1 Module binding and declaration} "]
type module_name = string option
external module_name_of_string_option :
  string option -> module_name = "%identity"
external string_option_of_module_name :
  module_name -> string option = "%identity"
module Md =
  struct
    let mk ?loc  ?attrs  (mod_name : string option Location.loc)
      (s : Ppxlib.module_type) =
      (Ppxlib.Ast_helper.Md.mk ?loc ?attrs
         (map_loc module_name_of_string_option mod_name) s : Ppxlib.module_declaration)
  end
module Mb =
  struct
    let mk ?loc  ?attrs  (mod_name : string option Location.loc)
      (s : Ppxlib.module_expr) =
      (Ppxlib.Ast_helper.Mb.mk ?loc ?attrs
         (map_loc module_name_of_string_option mod_name) s : Ppxlib.module_binding)
  end
[@@@ocaml.text " {1 Expressions} "]
module Exp =
  struct
    include Metapp_preutils.Exp
    let send ?loc  ?attrs  (expression : Ppxlib.expression)
      (str : Ppxlib.Ast_helper.str) =
      (Ppxlib.Ast_helper.Exp.send ?loc ?attrs expression str : Ppxlib.expression)
    let newtype ?loc  ?attrs  (name : Ppxlib.Ast_helper.str)
      (ty : Ppxlib.expression) =
      (Ppxlib.Ast_helper.Exp.newtype ?loc ?attrs name ty : Ppxlib.expression)
    let destruct_open (expression : Ppxlib.expression) =
      (match expression.pexp_desc with
       | Pexp_open (open_decl, expr) -> Some (open_decl, expr)
       | _ -> None : (Ppxlib.module_expr Opn.t * Ppxlib.expression) option)
    let open_ ?loc  ?attrs  (open_decl : Ppxlib.module_expr Opn.t)
      (expr : Ppxlib.expression) =
      (Ppxlib.Ast_helper.Exp.open_ ?loc ?attrs open_decl expr : Ppxlib.expression)
    let tuple_of_payload (payload : Ppxlib.payload) =
      (match of_payload payload with
       | { pexp_desc = Pexp_tuple tuple } -> tuple
       | e -> [e] : Ppxlib.expression list)
  end
[@@@ocaml.text " {1 Attribute management} "]
module Attr =
  struct
    let mk (name : Ppxlib.Ast_helper.str) (payload : Ppxlib.payload) =
      Ppxlib.Ast_helper.Attr.mk name payload
    let name (attribute : Ppxlib.attribute) =
      (attribute.attr_name : Ppxlib.Ast_helper.str)
    let payload (attribute : Ppxlib.attribute) =
      (attribute.attr_payload : Ppxlib.payload)
    let to_loc (attribute : Ppxlib.attribute) =
      (attribute.attr_loc : Location.t)
    let find (attr_name : string) (attributes : Ppxlib.attributes) =
      (List.find_opt
         (fun attribute -> String.equal (name attribute).txt attr_name)
         attributes : Ppxlib.attribute option)
    let chop (attr_name : string) (attributes : Ppxlib.attributes) =
      (extract_first
         (fun attribute ->
            if String.equal (name attribute).txt attr_name
            then Some attribute
            else None) attributes : (Ppxlib.attribute * Ppxlib.attributes)
                                      option)
    let get_derivers (attributes : Ppxlib.attributes) =
      (match find "deriving" attributes with
       | None -> None
       | Some derivers -> Some (Exp.tuple_of_payload (payload derivers)) : 
      Ppxlib.expression list option)
    let has_deriver (deriver_name : string) (attributes : Ppxlib.attributes)
      =
      (Option.bind (get_derivers attributes)
         (List.find_map
            (fun (e : Ppxlib.expression) ->
               match e.pexp_desc with
               | Pexp_ident { txt = Lident name;_} when
                   String.equal name deriver_name -> Some []
               | Pexp_apply
                   ({ pexp_desc = Pexp_ident { txt = Lident name;_} }, args)
                   when String.equal name deriver_name -> Some args
               | _ -> None)) : (Ppxlib.Asttypes.arg_label *
                                 Ppxlib.expression) list option)
  end
[@@@ocaml.text " {1 Pattern} "]
module Pat =
  struct
    include Metapp_preutils.Pat
    module Construct =
      struct
        module Arg =
          struct
            type t = (string Location.loc list * Ppxlib.pattern)
            let construct types pat = (types, pat)
            let destruct arg = arg
          end
      end
  end
[@@@ocaml.text " {1 Type declarations} "]
module Type =
  struct
    let has_deriver (deriver_name : string)
      (declarations : Ppxlib.type_declaration list) =
      (declarations |>
         (List.find_map
            (fun (decl : Ppxlib.type_declaration) ->
               Attr.has_deriver deriver_name decl.ptype_attributes)) : 
      (Ppxlib.Asttypes.arg_label * Ppxlib.expression) list option)
  end
[@@@ocaml.text " {1 Extension constructors} "]
module Te =
  struct
    type decl =
      {
      vars: Ast_helper.str list ;
      args: Ppxlib.constructor_arguments ;
      res: Ppxlib.core_type option }
    let destruct_decl (ec : Ppxlib.extension_constructor_kind) =
      match ec with
      | Pext_decl (vars, args, res) -> Some { vars; args; res }
      | Pext_rebind _ -> None
  end
[@@@ocaml.text " {1 Longident} "]
module Longident =
  struct
    include Longident
    let make ?prefix  name = make_ident ?prefix name
    let rec concat (a : t) (b : t) =
      (match b with
       | Lident b -> Ldot (a, b)
       | Ldot (m, name) -> Ldot ((concat a m), name)
       | Lapply (m, x) -> Lapply ((concat a m), x) : t)
    let rec compare (a : t) (b : t) =
      (match (a, b) with
       | (Lident a, Lident b) -> String.compare a b
       | (Ldot (am, ax), Ldot (bm, bx)) ->
           compare_pair compare String.compare (am, ax) (bm, bx)
       | (Lapply (af, am), Lapply (bf, bm)) ->
           compare_pair compare compare (af, am) (bf, bm)
       | (Lident _, (Ldot _ | Lapply _)) | (Ldot _, Lapply _) -> (-1)
       | (Lapply _, Ldot _) -> 1
       | ((Ldot _ | Lapply _), Lident _) -> 1 : int)
    let equal (a : t) (b : t) = ((compare a b) = 0 : bool)
    let rec hash (a : t) =
      (match a with
       | Lident a -> Hashtbl.hash (1, a)
       | Ldot (a, b) -> Hashtbl.hash ((hash a), b)
       | Lapply (m, x) -> Hashtbl.hash ((hash m), (hash x)) : int)
    let pp (fmt : Format.formatter) (ident : Longident.t) =
      Ppxlib.Pprintast.expression fmt
        (Ppxlib.Ast_helper.Exp.ident (mkloc ident))
    let show (ident : Longident.t) = (Format.asprintf "%a" pp ident : string)
    let of_module_expr_opt (module_expr : Ppxlib.module_expr) =
      (match module_expr.pmod_desc with
       | Pmod_ident { txt;_} -> Some txt
       | _ -> None : Longident.t option)
    let rec of_expression_opt (expression : Ppxlib.expression) =
      (match expression.pexp_desc with
       | Pexp_ident { txt;_} -> Some txt
       | Pexp_construct ({ txt;_}, None) -> Some txt
       | _ ->
           Option.bind (Exp.destruct_open expression)
             (fun (open_decl, expr) ->
                Option.bind (of_module_expr_opt open_decl.popen_expr)
                  (fun a -> Option.map (concat a) (of_expression_opt expr))) : 
      t option)
    let of_payload_opt (payload : Ppxlib.payload) =
      (match payload with
       | PStr ({ pstr_desc = Pstr_eval (expression, []) }::[]) ->
           of_expression_opt expression
       | _ -> None : t option)
    let of_payload (payload : Ppxlib.payload) =
      (match of_payload_opt payload with
       | Some ident -> ident
       | _ ->
           Location.raise_errorf ~loc:(!Ppxlib.Ast_helper.default_loc)
             "Identifier expected" : t)
  end
let mklid ?prefix  name = mkloc (Longident.make ?prefix name)
[@@@ocaml.text " {1 Mapper for [[@if bool]] notation} "]
class filter =
  let check_attr (attributes : Ppxlib.attributes) =
    match Attr.find "if" attributes with
    | None -> true
    | Some attr -> bool_of_payload (Attr.payload attr)
  in
  let rec check_pat (p : Ppxlib.pattern) =
    (match p.ppat_desc with
     | Ppat_constraint (p, _) -> check_pat p
     | _ -> false) || (check_attr p.ppat_attributes)
  in
  let check_value_binding (binding : Ppxlib.value_binding) =
    check_attr binding.pvb_attributes
  in
  let check_value_description (description : Ppxlib.value_description) =
    check_attr description.pval_attributes
  in let check_case (case : Ppxlib.case) = check_pat case.pc_lhs in
  let check_expr (e : Ppxlib.expression) = check_attr e.pexp_attributes in
  let check_pat_snd (type a) (arg : (a * Ppxlib.pattern)) =
    check_pat (snd arg)
  in
  let check_expr_snd (type a) (arg : (a * Ppxlib.expression)) =
    check_expr (snd arg)
  in
  let check_type_declaration (declaration : Ppxlib.type_declaration) =
    check_attr declaration.ptype_attributes
  in
  object
    inherit  Ppxlib.Ast_traverse.map as super
    method! pattern (p : Ppxlib.pattern) =
      (let p = super#pattern p in
       match p.ppat_desc with
       | Ppat_tuple args ->
           (match List.filter check_pat args with
            | [] -> Pat.of_unit ()
            | singleton::[] -> singleton
            | args -> { p with ppat_desc = (Ppat_tuple args) })
       | Ppat_construct (lid, Some arg) ->
           let (_, pat) = Pat.Construct.Arg.destruct arg in
           if check_pat pat
           then p
           else { p with ppat_desc = (Ppat_construct (lid, None)) }
       | Ppat_variant (label, Some arg) ->
           if check_pat arg
           then p
           else { p with ppat_desc = (Ppat_variant (label, None)) }
       | Ppat_record (fields, closed_flag) ->
           (match List.filter check_pat_snd fields with
            | [] -> { p with ppat_desc = Ppat_any }
            | fields ->
                { p with ppat_desc = (Ppat_record (fields, closed_flag)) })
       | Ppat_array args ->
           { p with ppat_desc = (Ppat_array (List.filter check_pat args)) }
       | Ppat_or (a, b) when not (check_pat a) -> b
       | Ppat_or (a, b) when not (check_pat b) -> a
       | _ -> p : Ppxlib.pattern)
    method! expression (e : Ppxlib.expression) =
      ((Ppxlib.Ast_helper.with_default_loc e.pexp_loc) @@
         (fun () ->
            let e = super#expression e in
            match e.pexp_desc with
            | Pexp_let (rec_flag, bindings, body) ->
                (match List.filter check_value_binding bindings with
                 | [] -> body
                 | bindings ->
                     {
                       e with
                       pexp_desc = (Pexp_let (rec_flag, bindings, body))
                     })
            | Pexp_fun (_label, _default, pat, body) when not (check_pat pat)
                -> body
            | Pexp_function cases ->
                {
                  e with
                  pexp_desc = (Pexp_function (List.filter check_case cases))
                }
            | Pexp_apply (f, args) ->
                let items =
                  List.filter check_expr_snd ((Ppxlib.Asttypes.Nolabel, f) ::
                    args) in
                (match extract_first
                         (function
                          | (Ppxlib.Asttypes.Nolabel, f) -> Some f
                          | _ -> None) items
                 with
                 | None ->
                     Location.raise_errorf
                       ~loc:(!Ppxlib.Ast_helper.default_loc)
                       "No function left in this application"
                 | Some (e, []) -> e
                 | Some (f, args) ->
                     { e with pexp_desc = (Pexp_apply (f, args)) })
            | Pexp_match (e, cases) ->
                {
                  e with
                  pexp_desc =
                    (Pexp_match (e, (List.filter check_case cases)))
                }
            | Pexp_try (e, cases) ->
                {
                  e with
                  pexp_desc = (Pexp_try (e, (List.filter check_case cases)))
                }
            | Pexp_tuple args ->
                (match List.filter check_expr args with
                 | [] -> Exp.of_unit ()
                 | singleton::[] -> singleton
                 | args -> { e with pexp_desc = (Pexp_tuple args) })
            | Pexp_construct (lid, Some arg) ->
                if check_expr arg
                then e
                else { e with pexp_desc = (Pexp_construct (lid, None)) }
            | Pexp_variant (label, Some arg) ->
                if check_expr arg
                then e
                else { e with pexp_desc = (Pexp_variant (label, None)) }
            | Pexp_record (fields, base) ->
                let base =
                  match base with
                  | Some expr when check_expr expr -> base
                  | _ -> None in
                let fields = List.filter check_expr_snd fields in
                (if fields = []
                 then
                   Location.raise_errorf
                     ~loc:(!Ppxlib.Ast_helper.default_loc)
                     "Cannot construct an empty record";
                 { e with pexp_desc = (Pexp_record (fields, base)) })
            | Pexp_array args ->
                {
                  e with
                  pexp_desc = (Pexp_array (List.filter check_expr args))
                }
            | Pexp_sequence (a, b) when not (check_expr a) -> b
            | Pexp_sequence (a, b) when not (check_expr b) -> a
            | _ -> e) : Ppxlib.expression)
    method! structure_item (item : Ppxlib.structure_item) =
      (let item = super#structure_item item in
       match item.pstr_desc with
       | Pstr_value (rec_flag, bindings) ->
           (match List.filter check_value_binding bindings with
            | [] -> Stri.of_list []
            | bindings ->
                { item with pstr_desc = (Pstr_value (rec_flag, bindings)) })
       | Pstr_primitive description when
           not (check_value_description description) -> Stri.of_list []
       | Pstr_type (rec_flag, declarations) ->
           {
             item with
             pstr_desc =
               (Pstr_type
                  (rec_flag,
                    (List.filter check_type_declaration declarations)))
           }
       | _ -> item : Ppxlib.structure_item)
    method! signature_item (item : Ppxlib.signature_item) =
      (let item = super#signature_item item in
       match item.psig_desc with
       | Psig_value description when
           not (check_value_description description) -> Sigi.of_list []
       | Psig_type (rec_flag, declarations) ->
           {
             item with
             psig_desc =
               (Psig_type
                  (rec_flag,
                    (List.filter check_type_declaration declarations)))
           }
       | _ -> item : Ppxlib.signature_item)
  end
[@@@ocaml.text " {1 Type construction} "]
module Typ =
  struct
    include Metapp_preutils.Typ
    let poly (names : Ppxlib.Ast_helper.str list) (ty : Ppxlib.core_type) =
      (Ppxlib.Ast_helper.Typ.poly names ty : Ppxlib.core_type)
    let poly_name name = (name : Ppxlib.Ast_helper.str).txt
  end
[@@@ocaml.text " {1 Row fields} "]
module Rf =
  struct
    type desc = Ppxlib.row_field_desc =
      | Rtag of Asttypes.label Location.loc * bool * Ppxlib.core_type list 
      | Rinherit of Ppxlib.core_type 
    let to_loc (rf : Ppxlib.row_field) = (rf.prf_loc : Location.t)
    let to_attributes (rf : Ppxlib.row_field) =
      (rf.prf_attributes : Ppxlib.attributes)
    let destruct (rf : Ppxlib.row_field) = (rf.prf_desc : desc)
    let tag ?loc:_loc  ?attrs  (label : Ppxlib.Asttypes.label Location.loc)
      (has_constant : bool) (args : Ppxlib.core_type list) =
      (Ppxlib.Ast_helper.Rf.tag ?loc:_loc ?attrs label has_constant args : 
      Ppxlib.row_field)
    let inherit_ ?loc:_loc  ?attrs:_attrs  (core_type : Ppxlib.core_type) =
      (Ppxlib.Ast_helper.Rf.mk ?loc:_loc ?attrs:_attrs (Rinherit core_type) : 
      Ppxlib.row_field)
  end
[@@@ocaml.text " {1 Object fields} "]
module Of =
  struct
    type t = Ppxlib.object_field
    type desc = Ppxlib.object_field_desc =
      | Otag of Asttypes.label Location.loc * Ppxlib.core_type 
      | Oinherit of Ppxlib.core_type 
    let to_loc (of_ : t) = (of_.pof_loc : Location.t)
    let to_attributes (of_ : t) = (of_.pof_attributes : Ppxlib.attributes)
    let destruct (of_ : t) = (of_.pof_desc : desc)
    let tag ?loc:_loc  ?attrs  (label : Asttypes.label Location.loc)
      (ty : Ppxlib.core_type) =
      (Ppxlib.Ast_helper.Of.tag ?loc:_loc ?attrs label ty : t)
    let inherit_ ?loc:_loc  ?attrs:_attrs  (_ty : Ppxlib.core_type) =
      (Ppxlib.Ast_helper.Of.mk ?loc:_loc ?attrs:_attrs (Oinherit _ty) : 
      t)
  end
[@@@ocaml.text " {1 Module expressions} "]
type functor_parameter = Ppxlib.functor_parameter =
  | Unit 
  | Named of string option Location.loc * Ppxlib.module_type 
module type FunctorS  =
  sig
    type t
    val functor_ :
      ?loc:Location.t ->
        ?attrs:Ppxlib.attributes -> functor_parameter -> t -> t
    val destruct_functor : t -> (functor_parameter * t) option
  end
module type ModS  =
  sig include ExtensibleS include FunctorS with type  t :=  t end
module Mod =
  struct
    include Metapp_preutils.Mod
    let functor_ ?loc  ?attrs  (parameter : functor_parameter)
      (body : Ppxlib.module_expr) =
      (Ppxlib.Ast_helper.Mod.functor_ ?loc ?attrs parameter body : Ppxlib.module_expr)
    let destruct_functor (modtype : Ppxlib.module_expr) =
      (match modtype.pmod_desc with
       | Pmod_functor (f, s) -> Some (f, s)
       | _ -> None : (functor_parameter * Ppxlib.module_expr) option)
  end
[@@@ocaml.text " {1 Module types} "]
module Mty =
  struct
    include Metapp_preutils.Mty
    let functor_ ?loc  ?attrs  (parameter : functor_parameter)
      (body : Ppxlib.module_type) =
      (Ppxlib.Ast_helper.Mty.functor_ ?loc ?attrs parameter body : Ppxlib.module_type)
    let destruct_functor (modtype : Ppxlib.module_type) =
      (match modtype.pmty_desc with
       | Pmty_functor (f, s) -> Some (f, s)
       | _ -> None : (functor_parameter * Ppxlib.module_type) option)
  end
let _anonymous_module_unsupported =
  "Anonymous modules are not supported with OCaml <4.10.0"
module Types =
  struct
    [@@@ocaml.text " {1 Signature type destruction} "]
    type visibility = Types.visibility =
      | Exported 
      | Hidden 
    module Sigi =
      struct
        type sig_type =
          {
          id: Ident.t ;
          decl: Types.type_declaration ;
          rec_status: Types.rec_status ;
          visibility: visibility }
        let sig_type (sig_type : sig_type) =
          (Sig_type
             ((sig_type.id), (sig_type.decl), (sig_type.rec_status),
               (sig_type.visibility)) : Types.signature_item)
        let destruct_sig_type (item : Types.signature_item) =
          (match item with
           | Sig_type (id, decl, rec_status, visibility) ->
               Some { id; decl; rec_status; visibility }
           | _ -> None : sig_type option)
      end
    [@@@ocaml.text " {1 Module types in Types} "]
    include
      struct
        type functor_parameter = Types.functor_parameter =
          | Unit 
          | Named of Ident.t option * Types.module_type 
      end
    module Mty =
      struct
        let functor_ (parameter : functor_parameter)
          (body : Types.module_type) =
          (Mty_functor (parameter, body) : Types.module_type)
        let destruct_functor (modtype : Types.module_type) =
          (match modtype with | Mty_functor (f, s) -> Some (f, s) | _ -> None : 
          (functor_parameter * Types.module_type) option)
        let destruct_alias (modtype : Types.module_type) =
          (match modtype with | Mty_alias p -> Some p | _ -> None : Path.t
                                                                    option)
      end
    type variant_representation = Types.variant_representation =
      | Variant_regular 
      | Variant_unboxed 
    let destruct_type_variant type_kind =
      match type_kind with
      | Types.Type_variant (list, repr) -> Some (list, repr)
      | _ -> None
    let destruct_tpackage (type_desc : Types.type_desc) =
      match type_desc with
      | Tpackage (path, list) -> Some (path, list)
      | _ -> None
    let get_desc (type_expr : Types.type_expr) =
      (Types.get_desc type_expr : Types.type_desc)
    let get_level (type_expr : Types.type_expr) =
      (Types.get_level type_expr : int)
    let get_scope (type_expr : Types.type_expr) =
      (Types.get_scope type_expr : int)
    let get_id (type_expr : Types.type_expr) =
      (Types.get_level type_expr : int)
  end
[@@@ocaml.text " {1 With constraint} "]
module With =
  struct
    let typesubst ?t  (decl : Ppxlib.type_declaration) =
      (let t =
         match t with | None -> lid_of_str decl.ptype_name | Some t -> t in
       Ppxlib.Pwith_typesubst (t, decl) : Ppxlib.with_constraint)
    let destruct_typesubst (cstr : Ppxlib.with_constraint) =
      (match cstr with
       | Pwith_typesubst (t, decl) -> Some (t, decl)
       | _ -> None : (Ppxlib.Ast_helper.lid * Ppxlib.type_declaration) option)
    let modsubst (x : Ppxlib.Ast_helper.lid) (y : Ppxlib.Ast_helper.lid) =
      (Ppxlib.Pwith_modsubst (x, y) : Ppxlib.with_constraint)
    let destruct_modsubst (cstr : Ppxlib.with_constraint) =
      (match cstr with | Pwith_modsubst (x, y) -> Some (x, y) | _ -> None : 
      (Ppxlib.Ast_helper.lid * Ppxlib.Ast_helper.lid) option)
  end
