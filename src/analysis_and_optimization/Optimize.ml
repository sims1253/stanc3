(** Code for optimization passes on the MIR *)

open Std
open Common
open Middle
open Mir_utils
open Dataflow_types

(** Apply the transformation to each function body and to the rest of the
    program as one block. *)
let transform_program (mir : Program.Typed.t)
    (transform : Stmt.Located.t -> Stmt.Located.t) : Program.Typed.t =
  let packed_prog_body =
    transform
      { pattern=
          SList
            (List.map
               ~f:(fun x -> Stmt.{pattern= SList x; meta= Location_span.empty})
               [ mir.prepare_data; mir.transform_inits; mir.log_prob
               ; mir.reverse_mode_log_prob; mir.generate_quantities ])
      ; meta= Location_span.empty } in
  let transformed_prog_body = transform packed_prog_body in
  let transformed_functions =
    List.map mir.functions_block ~f:(fun fs ->
        Program.{fs with fdbody= Option.map ~f:transform fs.fdbody}) in
  match transformed_prog_body with
  | { pattern=
        SList
          [ {pattern= SList prepare_data'; _}
          ; {pattern= SList transform_inits'; _}; {pattern= SList log_prob'; _}
          ; {pattern= SList reverse_mode_log_prob'; _}
          ; {pattern= SList generate_quantities'; _} ]
    ; _ } ->
      { mir with
        functions_block= transformed_functions
      ; prepare_data= prepare_data'
      ; transform_inits= transform_inits'
      ; log_prob= log_prob'
      ; reverse_mode_log_prob= reverse_mode_log_prob'
      ; generate_quantities= generate_quantities' }
  | _ ->
      ICE.internal_error
        "Something went wrong with program transformation packing!"
      [@coverage off]

(** Apply the transformation to each function body and to each program block
    separately. *)
let transform_program_blockwise (mir : Program.Typed.t)
    (transform :
      Stmt.Located.t Program.fun_def option -> Stmt.Located.t -> Stmt.Located.t)
    : Program.Typed.t =
  let transform' fd s =
    match transform fd {pattern= SList s; meta= Location_span.empty} with
    | {pattern= SList l; _} -> l
    | _ ->
        ICE.internal_error
          "Something went wrong with program transformation packing!"
        [@coverage off] in
  let transformed_functions =
    List.map mir.functions_block ~f:(fun fs ->
        Program.{fs with fdbody= Option.map ~f:(transform (Some fs)) fs.fdbody})
  in
  { mir with
    functions_block= transformed_functions
  ; prepare_data= transform' None mir.prepare_data
  ; transform_inits= transform' None mir.transform_inits
  ; log_prob= transform' None mir.log_prob
  ; reverse_mode_log_prob= transform' None mir.reverse_mode_log_prob
  ; generate_quantities= transform' None mir.generate_quantities }

let map_no_loc l =
  List.map ~f:(fun s -> Stmt.{pattern= s; meta= Location_span.empty}) l

let slist_no_loc l = Stmt.Pattern.SList (map_no_loc l)
let block_no_loc l = Stmt.Pattern.Block (map_no_loc l)

let slist_concat_no_loc l stmt =
  match l with [] -> stmt | l -> slist_no_loc (l @ [stmt])

let gen_inline_var (name : string) (id_var : string) =
  Gensym.generate ~prefix:("inline_" ^ name ^ "_" ^ id_var ^ "_") ()

let replace_fresh_local_vars (fname : string) stmt =
  let f (m : string String.Map.t) = function
    | Stmt.Pattern.Decl {decl_adtype; decl_type; decl_id; initialize} ->
        let new_name =
          match String.Map.find_opt decl_id m with
          | Some existing -> existing
          | None -> gen_inline_var fname decl_id in
        ( Stmt.Pattern.Decl
            {decl_adtype; decl_id= new_name; decl_type; initialize}
        , String.Map.add m ~key:decl_id ~data:new_name )
    | Stmt.Pattern.For {loopvar; lower; upper; body} ->
        let new_name =
          match String.Map.find_opt loopvar m with
          | Some existing -> existing
          | None -> gen_inline_var fname loopvar in
        ( Stmt.Pattern.For {loopvar= new_name; lower; upper; body}
        , String.Map.add m ~key:loopvar ~data:new_name )
    | Assignment (lhs, type_, e) ->
        let update_name var_name =
          match String.Map.find_opt var_name m with
          | None -> var_name
          | Some var_name' -> var_name' in
        let lhs' = Middle.Stmt.Helpers.map_lhs_variable ~f:update_name lhs in
        (Stmt.Pattern.Assignment (lhs', type_, e), m)
    | x -> (x, m) in
  let s, m = map_rec_state_stmt_loc f String.Map.empty stmt in
  name_subst_stmt m s

let subst_args_stmt args es =
  let m = String.Map.of_list (List.combine args es) in
  subst_stmt m

(** Count the number of returns that happen in a statement *)
let rec count_returns Stmt.{pattern; _} : int =
  Stmt.Pattern.fold Fun.const
    (fun acc -> function
      | Stmt.{pattern= Return _; _} -> acc + 1
      | stmt -> acc + count_returns stmt)
    0 pattern

(* The strategy here is to wrap the function body in a dummy loop, then replace
   returns with breaks. One issue is early return from internal loops - in those
   cases, a break would only break out of the inner loop. The solution is a flag
   variable to indicate whether a 'return' break has been called, and then to
   check if that flag is set after each loop. Then, if a 'return' break is
   called from an inner loop, there's a cascade of breaks all the way out of the
   dummy loop. *)
let handle_early_returns (fname : string) opt_var stmt =
  let returned = gen_inline_var fname "early_ret_check" in
  let generate_inner_breaks num_returns stmt_pattern =
    match stmt_pattern with
    | Stmt.Pattern.Return opt_ret -> (
        match (opt_var, opt_ret) with
        | None, None when num_returns > 1 -> Stmt.Pattern.Break
        | None, None -> Stmt.Pattern.Block []
        | Some name, Some e when num_returns > 1 ->
            SList
              [ Stmt.
                  { pattern=
                      Assignment
                        ( Stmt.Helpers.lvariable returned
                        , UInt
                        , Expr.
                            { pattern= Lit (Int, "1")
                            ; meta=
                                Expr.Typed.Meta.
                                  { type_= UInt
                                  ; adlevel= DataOnly
                                  ; loc= Location_span.empty } } )
                  ; meta= Location_span.empty }
              ; Stmt.
                  { pattern=
                      Assignment
                        (Stmt.Helpers.lvariable name, Expr.Typed.type_of e, e)
                  ; meta= Location_span.empty }
              ; {pattern= Break; meta= Location_span.empty} ]
        | Some name, Some e ->
            Assignment (Stmt.Helpers.lvariable name, Expr.Typed.type_of e, e)
        | Some _, None ->
            ICE.internal_error
              "Function should return a value but found an empty return \
               statement." [@coverage off]
        | None, Some _ ->
            ICE.internal_error
              "Expected a void function but found a non-empty return statement."
            [@coverage off])
    | Stmt.Pattern.For _ as loop when num_returns > 1 ->
        Stmt.Pattern.SList
          [ Stmt.{pattern= loop; meta= Location_span.empty}
          ; Stmt.
              { pattern=
                  IfElse
                    ( Expr.
                        { pattern= Var returned
                        ; meta=
                            Expr.Typed.Meta.
                              { type_= UInt
                              ; adlevel= DataOnly
                              ; loc= Location_span.empty } }
                    , {pattern= Break; meta= Location_span.empty}
                    , None )
              ; meta= Location_span.empty } ]
    | x -> x in
  let num_returns = count_returns stmt in
  if num_returns > 1 then
    Stmt.Pattern.SList
      [ Stmt.
          { pattern=
              Decl
                { decl_adtype= DataOnly
                ; decl_id= returned
                ; decl_type= Sized SInt
                ; initialize= Default }
          ; meta= Location_span.empty }
      ; Stmt.
          { pattern=
              Assignment
                ( Stmt.Helpers.lvariable returned
                , UInt
                , Expr.
                    { pattern= Lit (Int, "0")
                    ; meta=
                        Expr.Typed.Meta.
                          { type_= UInt
                          ; adlevel= DataOnly
                          ; loc= Location_span.empty } } )
          ; meta= Location_span.empty }
      ; Stmt.
          { pattern=
              Stmt.Pattern.For
                { loopvar= gen_inline_var fname "iterator"
                ; lower=
                    Expr.
                      { pattern= Lit (Int, "1")
                      ; meta=
                          Expr.Typed.Meta.
                            { type_= UInt
                            ; adlevel= DataOnly
                            ; loc= Location_span.empty } }
                ; upper=
                    { pattern= Lit (Int, "1")
                    ; meta=
                        { type_= UInt
                        ; adlevel= DataOnly
                        ; loc= Location_span.empty } }
                ; body=
                    map_rec_stmt_loc (generate_inner_breaks num_returns) stmt }
          ; meta= Location_span.empty } ]
  else (map_rec_stmt_loc (generate_inner_breaks num_returns) stmt).pattern

let inline_list f es =
  let dse_list = List.map ~f es in
  (* function arguments are evaluated from right to left in C++, so we need to
     reverse *)
  let d_list =
    List.concat (List.rev (List.map ~f:(function x, _, _ -> x) dse_list)) in
  let s_list =
    List.concat (List.rev (List.map ~f:(function _, x, _ -> x) dse_list)) in
  let es = List.map ~f:(function _, _, x -> x) dse_list in
  (d_list, s_list, es)

let compute_suffix_and_name propto suffix fname =
  let open Fun_kind in
  match suffix with
  | FnLpdf propto' when propto' && propto ->
      ( FnLpdf true
      , with_unnormalized_suffix fname |> Option.value ~default:fname )
  | FnLpdf _ -> (FnLpdf false, fname)
  | FnLpmf propto' when propto' && propto ->
      ( FnLpmf true
      , with_unnormalized_suffix fname |> Option.value ~default:fname )
  | FnLpmf _ -> (FnLpmf false, fname)
  | _ -> (suffix, fname)

(* Triple is (declaration list, statement list, return expression) *)
let rec inline_function_expression propto adt fim (Expr.{pattern; _} as e) =
  match pattern with
  | Var _ -> ([], [], e)
  | Lit (_, _) -> ([], [], e)
  | Promotion (expr, ut, ad) ->
      let d, sl, expr' = inline_function_expression propto adt fim expr in
      (d, sl, {e with pattern= Promotion (expr', ut, ad)})
  | FunApp (kind, es) -> (
      let d_list, s_list, es =
        inline_list (inline_function_expression propto adt fim) es in
      match kind with
      | CompilerInternal _ ->
          (d_list, s_list, {e with pattern= FunApp (kind, es)})
      | StanLib (fname, suffix, mem) ->
          let suffix, _ = compute_suffix_and_name propto suffix fname in
          ( d_list
          , s_list
          , {e with pattern= FunApp (Fun_kind.StanLib (fname, suffix, mem), es)}
          )
      | UserDefined (fname, suffix) -> (
          let suffix, fname' = compute_suffix_and_name propto suffix fname in
          match String.Map.find_opt fname' fim with
          | None ->
              ( d_list
              , s_list
              , { e with
                  pattern= FunApp (Fun_kind.UserDefined (fname, suffix), es) }
              )
          | Some (rt, args, body) ->
              let inline_return_name = gen_inline_var fname "return" in
              let handle =
                handle_early_returns fname (Some inline_return_name) in
              let d_list2, s_list2, (e : Expr.Typed.t) =
                let decl_type =
                  Option.map ~f:Mir_utils.unsafe_unsized_to_sized_type rt
                  |> Option.get in
                ( [ Stmt.Pattern.Decl
                      { decl_adtype=
                          UnsizedType.fill_adtype_for_type adt
                            (Type.to_unsized decl_type)
                      ; decl_id= inline_return_name
                      ; decl_type
                      ; initialize= Uninit } ]
                  (* We should minimize the code that's having its variables
                     replaced to avoid conflict with the (two) new dummy
                     variables introduced by inlining *)
                , [ handle
                      (subst_args_stmt args es
                         (replace_fresh_local_vars fname body)) ]
                , { pattern= Var inline_return_name
                  ; meta=
                      Expr.Typed.Meta.
                        { type_= Type.to_unsized decl_type
                        ; adlevel= adt
                        ; loc= Location_span.empty } } ) in
              let d_list = d_list @ d_list2 in
              let s_list = s_list @ s_list2 in
              (d_list, s_list, e)))
  | TernaryIf (e1, e2, e3) ->
      let dl1, sl1, e1 = inline_function_expression propto adt fim e1 in
      let dl2, sl2, e2 = inline_function_expression propto adt fim e2 in
      let dl3, sl3, e3 = inline_function_expression propto adt fim e3 in
      ( dl1 @ dl2 @ dl3
      , sl1
        @ [ Stmt.(
              Pattern.IfElse
                ( e1
                , {pattern= block_no_loc sl2; meta= Location_span.empty}
                , Some {pattern= block_no_loc sl3; meta= Location_span.empty} ))
          ]
      , {e with pattern= TernaryIf (e1, e2, e3)} )
  | Indexed (e', i_list) ->
      let dl, sl, e' = inline_function_expression propto adt fim e' in
      let d_list, s_list, i_list =
        inline_list (inline_function_index propto adt fim) i_list in
      (d_list @ dl, s_list @ sl, {e with pattern= Indexed (e', i_list)})
  | TupleProjection (e', ix) ->
      let dl, sl, e' = inline_function_expression propto adt fim e' in
      (dl, sl, {e with pattern= TupleProjection (e', ix)})
  | EAnd (e1, e2) ->
      let dl1, sl1, e1 = inline_function_expression propto adt fim e1 in
      let dl2, sl2, e2 = inline_function_expression propto adt fim e2 in
      let sl2 =
        [ Stmt.(
            Pattern.IfElse
              ( e1
              , {pattern= Block (map_no_loc sl2); meta= Location_span.empty}
              , None )) ] in
      (dl1 @ dl2, sl1 @ sl2, {e with pattern= EAnd (e1, e2)})
  | EOr (e1, e2) ->
      let dl1, sl1, e1 = inline_function_expression propto adt fim e1 in
      let dl2, sl2, e2 = inline_function_expression propto adt fim e2 in
      let sl2 =
        [ Stmt.(
            Pattern.IfElse
              ( e1
              , {pattern= Skip; meta= Location_span.empty}
              , Some {pattern= Block (map_no_loc sl2); meta= Location_span.empty}
              )) ] in
      (dl1 @ dl2, sl1 @ sl2, {e with pattern= EOr (e1, e2)})

and inline_function_index propto adt fim i =
  match i with
  | All -> ([], [], All)
  | Single e ->
      let dl, sl, e = inline_function_expression propto adt fim e in
      (dl, sl, Single e)
  | Upfrom e ->
      let dl, sl, e = inline_function_expression propto adt fim e in
      (dl, sl, Upfrom e)
  | Between (e1, e2) ->
      let dl1, sl1, e1 = inline_function_expression propto adt fim e1 in
      let dl2, sl2, e2 = inline_function_expression propto adt fim e2 in
      (dl1 @ dl2, sl1 @ sl2, Between (e1, e2))
  | MultiIndex e ->
      let dl, sl, e = inline_function_expression propto adt fim e in
      (dl, sl, MultiIndex e)

let rec inline_function_statement propto adt fim Stmt.{pattern; meta} =
  Stmt.
    { pattern=
        (match pattern with
        | Assignment (lhs, ut, e2) ->
            let e1 = Middle.Stmt.Helpers.expr_of_lvalue lhs ~meta:e2.meta in
            (* This inner e2 is wrong. We are giving the wrong type to Var x.
               But it doesn't really matter as we discard it later. *)
            let dl1, sl1, e1 = inline_function_expression propto adt fim e1 in
            let dl2, sl2, e2 = inline_function_expression propto adt fim e2 in
            let lhs' =
              match Middle.Stmt.Helpers.lvalue_of_expr_opt e1 with
              | Some x -> x
              | None ->
                  ICE.internal_error
                    "Internal error in inline optimization: lhs could not be \
                     converted round-trip to expression" [@coverage off] in
            slist_concat_no_loc
              (dl2 @ dl1 @ sl2 @ sl1)
              (Assignment (lhs', ut, e2))
        | TargetPE e ->
            let d, s, e = inline_function_expression propto adt fim e in
            slist_concat_no_loc (d @ s) (TargetPE e)
        | JacobianPE e ->
            let d, s, e = inline_function_expression propto adt fim e in
            slist_concat_no_loc (d @ s) (JacobianPE e)
        | NRFunApp (kind, exprs) ->
            let d_list, s_list, es =
              inline_list (inline_function_expression propto adt fim) exprs
            in
            slist_concat_no_loc (d_list @ s_list)
              (match kind with
              | CompilerInternal _ | StanLib _ -> NRFunApp (kind, es)
              | UserDefined (s, _) -> (
                  match String.Map.find_opt s fim with
                  | None -> NRFunApp (kind, es)
                  | Some (_, args, b) ->
                      let b = replace_fresh_local_vars s b in
                      let b = handle_early_returns s None b in
                      (subst_args_stmt args es
                         {pattern= b; meta= Location_span.empty})
                        .pattern))
        | Return e -> (
            match e with
            | None -> Return None
            | Some expr ->
                let d, s, e = inline_function_expression propto adt fim expr in
                slist_concat_no_loc (d @ s) (Return (Some e)))
        | IfElse (expr, s1, s2) ->
            let d, s, e = inline_function_expression propto adt fim expr in
            slist_concat_no_loc (d @ s)
              (IfElse
                 ( e
                 , inline_function_statement propto adt fim s1
                 , Option.map ~f:(inline_function_statement propto adt fim) s2
                 ))
        | While (expr, stmt) ->
            let d', s', e = inline_function_expression propto adt fim expr in
            slist_concat_no_loc (d' @ s')
              (While
                 ( e
                 , if List.is_empty s' then
                     inline_function_statement propto adt fim stmt
                   else
                     { pattern=
                         Block
                           ([inline_function_statement propto adt fim stmt]
                           @ map_no_loc s')
                     ; meta= Location_span.empty } ))
        | For {loopvar; lower; upper; body} ->
            let d_lower, s_lower, lower =
              inline_function_expression propto adt fim lower in
            let d_upper, s_upper, upper =
              inline_function_expression propto adt fim upper in
            slist_concat_no_loc
              (d_lower @ d_upper @ s_lower @ s_upper)
              (For
                 { loopvar
                 ; lower
                 ; upper
                 ; body=
                     (if List.is_empty s_upper then
                        inline_function_statement propto adt fim body
                      else
                        { pattern=
                            Block
                              ([inline_function_statement propto adt fim body]
                              @ map_no_loc s_upper)
                        ; meta= Location_span.empty }) })
        | Profile (name, l) ->
            Profile
              (name, List.map l ~f:(inline_function_statement propto adt fim))
        | Block l ->
            Block (List.map l ~f:(inline_function_statement propto adt fim))
        | SList l ->
            SList (List.map l ~f:(inline_function_statement propto adt fim))
        | Decl {decl_adtype; decl_id; decl_type; initialize= Assign expr} ->
            let d, s, e = inline_function_expression propto adt fim expr in
            slist_concat_no_loc (d @ s)
              (Decl {decl_adtype; decl_id; decl_type; initialize= Assign e})
        | Decl r -> Decl r
        | Skip -> Skip
        | Break -> Break
        | Continue -> Continue)
    ; meta }

let create_function_inline_map adt l =
  let f accum Program.{fdname; fdargs; fdbody; fdrt; _} =
    match fdbody with
    | None -> accum
    | Some fdbody -> (
        let create_data propto =
          ( Option.map
              ~f:(fun x -> Type.Unsized x)
              (UnsizedType.returntype_to_type_opt fdrt)
          , List.map ~f:(fun (_, name, _) -> name) fdargs
          , inline_function_statement propto adt accum fdbody ) in
        match Middle.Fun_kind.with_unnormalized_suffix fdname with
        | None ->
            let data = create_data true in
            if String.Map.mem fdname accum then accum
            else String.Map.add accum ~key:fdname ~data
        | Some fdname' ->
            let data = create_data false in
            let data' = create_data true in
            let m = String.Map.of_list [(fdname, data); (fdname', data')] in
            String.Map.union accum m ~f:(fun _ v1 _ -> Some v1)) in
  List.fold_left l ~init:String.Map.empty ~f

let function_inlining (mir : Program.Typed.t) =
  (* We add only the functions with a single definition to the inline map.
     Overloaded functions cannot be inlined. *)
  let can_inline =
    List.fold_left mir.functions_block ~init:String.Map.empty
      ~f:(fun accum Program.{fdname; _} ->
        String.Map.update accum ~key:fdname ~f:(fun o ->
            Some (Option.value_map o ~default:true ~f:(fun _ -> false)))) in
  let inlineable_functions =
    List.filter mir.functions_block ~f:(fun Program.{fdname; _} ->
        String.Map.find fdname can_inline) in
  let dataonly_inline_map =
    create_function_inline_map UnsizedType.DataOnly inlineable_functions in
  let autodiff_inline_map =
    create_function_inline_map UnsizedType.AutoDiffable inlineable_functions
  in
  let dataonly_inline_function_statements =
    List.map
      ~f:
        (inline_function_statement true UnsizedType.DataOnly dataonly_inline_map)
  in
  let autodiffable_inline_function_statements =
    List.map
      ~f:
        (inline_function_statement true UnsizedType.AutoDiffable
           autodiff_inline_map) in
  { mir with
    transform_inits= autodiffable_inline_function_statements mir.transform_inits
  ; unconstrain_array=
      autodiffable_inline_function_statements mir.unconstrain_array
  ; log_prob= autodiffable_inline_function_statements mir.log_prob
  ; reverse_mode_log_prob=
      autodiffable_inline_function_statements mir.reverse_mode_log_prob
  ; generate_quantities=
      dataonly_inline_function_statements mir.generate_quantities }

let rec contains_top_break_or_continue Stmt.{pattern; _} =
  match pattern with
  | Break | Continue -> true
  | Assignment (_, _, _)
   |TargetPE _ | JacobianPE _
   |NRFunApp (_, _)
   |Return _ | Decl _
   |While (_, _)
   |For _ | Skip ->
      false
  | Profile (_, l) | Block l | SList l ->
      List.exists l ~f:contains_top_break_or_continue
  | IfElse (_, b1, b2) -> (
      contains_top_break_or_continue b1
      ||
      match b2 with
      | None -> false
      | Some b -> contains_top_break_or_continue b)

let unroll_static_limit = 32

let unroll_static_loops_statement _ =
  let f stmt =
    match stmt with
    | Stmt.Pattern.For {loopvar; lower; upper; body} -> (
        let lower = Partial_evaluator.try_eval_expr lower in
        let upper = Partial_evaluator.try_eval_expr upper in
        match
          (contains_top_break_or_continue body, lower.pattern, upper.pattern)
        with
        | false, Lit (Int, low_str), Lit (Int, up_str) ->
            let low = Int.of_string low_str in
            let up = Int.of_string up_str in
            if up - low > unroll_static_limit then stmt
            else
              let range =
                List.map
                  ~f:(fun i ->
                    Expr.
                      { pattern= Lit (Int, Int.to_string i)
                      ; meta=
                          Expr.Typed.Meta.
                            { type_= UInt
                            ; loc= Location_span.empty
                            ; adlevel= DataOnly } })
                  (List.range low (up + 1)) in
              let stmts =
                List.map
                  ~f:(fun i ->
                    subst_args_stmt [loopvar] [i]
                      {pattern= body.pattern; meta= Location_span.empty})
                  range in
              Stmt.Pattern.SList stmts
        | _ -> stmt)
    | _ -> stmt in
  top_down_map_rec_stmt_loc f

let static_loop_unrolling mir =
  transform_program_blockwise mir unroll_static_loops_statement

let unroll_loop_one_step_statement _ =
  let f stmt : (_, Stmt.Located.t) Stmt.Pattern.t =
    match stmt with
    | Stmt.Pattern.For {loopvar; lower; upper; body}
      when not (contains_top_break_or_continue body) ->
        IfElse
          ( Expr.
              { lower with
                pattern= FunApp (StanLib ("Geq__", FnPlain, AoS), [upper; lower])
              }
          , { pattern=
                (let body_unrolled =
                   subst_args_stmt [loopvar] [lower]
                     {pattern= body.pattern; meta= Location_span.empty} in
                 let (body' : Stmt.Located.t) =
                   { pattern=
                       Stmt.Pattern.For
                         { loopvar
                         ; upper
                         ; body
                         ; lower=
                             { lower with
                               pattern=
                                 FunApp
                                   ( StanLib ("Plus__", FnPlain, AoS)
                                   , [lower; Expr.Helpers.loop_bottom] ) } }
                   ; meta= Location_span.empty } in
                 match body_unrolled.pattern with
                 | Block stmts -> Block (stmts @ [body'])
                 | _ -> Stmt.Pattern.Block [body_unrolled; body'])
            ; meta= Location_span.empty }
          , None )
    | While (e, body) when not (contains_top_break_or_continue body) ->
        IfElse
          ( e
          , { pattern= Block [body; {body with pattern= While (e, body)}]
            ; meta= Location_span.empty }
          , None )
    | _ -> stmt in
  map_rec_stmt_loc f

let one_step_loop_unrolling mir =
  transform_program_blockwise mir unroll_loop_one_step_statement

let rec expr_any pred (e : Expr.Typed.t) =
  match e.pattern with
  | Indexed (e, is) -> expr_any pred e || List.exists ~f:(idx_any pred) is
  | _ -> pred e || Expr.Pattern.fold (accum_any pred) false e.pattern

and idx_any pred (i : Expr.Typed.t Index.t) =
  Index.fold (accum_any pred) false i

and accum_any pred b e = b || expr_any pred e

let can_side_effect_top_expr (e : Expr.Typed.t) =
  match e.pattern with
  | FunApp ((UserDefined (_, FnTarget) | StanLib (_, FnTarget, _)), _) -> true
  | FunApp (CompilerInternal internal_fn, _) ->
      Internal_fun.can_side_effect internal_fn
  | _ -> false

let cannot_duplicate_expr ?(preserve_stability = false) (e : Expr.Typed.t) =
  let pred e =
    can_side_effect_top_expr e
    || (match e.pattern with
      | FunApp ((UserDefined (_, FnRng) | StanLib (_, FnRng, _)), _) -> true
      | _ -> false)
    || (preserve_stability && UnsizedType.is_autodiffable e.meta.type_) in
  expr_any pred e

let cannot_remove_expr (e : Expr.Typed.t) = expr_any can_side_effect_top_expr e

(* Rewrites e.g. [for (n in 1:N) target += normal_lpdf(y[n] | mu[n], sigma)] to
   [target += normal_lpdf(y | mu, sigma)]. Tilde statements have the same MIR
   shape, and the proportionality flag is part of the function suffix, so they
   are covered too.

   Every argument must be a side-effect-free scalar that is invariant in the
   loop variable, or exactly [x[n]]. An [x[n]] argument becomes the slice
   [x[lower:upper]], or [x] alone when the range provably spans the declaration.
   At least one argument must vary with the loop.

   The rewritten is typechecked against the Stan Math signatures so that the
   signature table determines which densities vectorize. *)
let vectorize_loops (mir : Program.Typed.t) =
  let outer_size st = List.hd (SizedType.get_dims st) in
  let trusted_sizes =
    List.filter_map mir.input_vars ~f:(fun (name, _, st) ->
        Option.map (outer_size st) ~f:(fun d -> (name, d)))
    @ List.filter_map mir.output_vars ~f:(fun (name, _, ov) ->
        match ov.Program.out_block with
        | GeneratedQuantities -> None
        | Parameters | TransformedParameters ->
            Option.map (outer_size ov.out_constrained_st) ~f:(fun d ->
                (name, d)))
    @ List.filter_map mir.prepare_data ~f:(fun stmt ->
        match stmt.Stmt.pattern with
        | Decl {decl_id; decl_type= Type.Sized st; _} ->
            Option.map (outer_size st) ~f:(fun d -> (decl_id, d))
        | _ -> None)
    |> String.Map.of_list in
  let spans_declaration sizes ~lower ~upper (base : Expr.Typed.t) =
    Expr.Typed.equal lower Expr.Helpers.loop_bottom
    &&
    match base.pattern with
    | Var v ->
        Option.exists (Expr.Typed.equal upper) (String.Map.find_opt v sizes)
    | _ -> false in
  let vectorize_arg sizes ~loopvar ~lower ~upper (arg : Expr.Typed.t) =
    match arg with
    | { pattern=
          Indexed (({pattern= Var _; _} as base), [Single {pattern= Var v; _}])
      ; _ }
      when v = loopvar ->
        Some
          (`Sliced
             (if spans_declaration sizes ~lower ~upper base then base
              else
                Expr.Helpers.add_int_index base (Index.Between (lower, upper))))
    | {meta= {type_= UInt | UReal | UComplex; _}; _}
      when (not (Set.Poly.mem loopvar (expr_var_names_set arg)))
           && not (cannot_remove_expr arg) ->
        Some (`Invariant arg)
    | _ -> None in
  let vectorize_for sizes ~loopvar ~lower ~upper (body : Stmt.Located.t) =
    let open Stdlib.Option.Syntax in
    let* stmt =
      match body.Stmt.pattern with
      | Block [s] | SList [s] -> Some s
      | TargetPE _ -> Some body
      | _ -> None in
    let* e, name, suffix, mem, args =
      match stmt.Stmt.pattern with
      | TargetPE
          ({ pattern=
               FunApp
                 (StanLib (name, ((FnLpdf _ | FnLpmf _) as suffix), mem), args)
           ; _ } as e) ->
          Some (e, name, suffix, mem, args)
      | _ -> None in
    let* classified =
      List.map args ~f:(vectorize_arg sizes ~loopvar ~lower ~upper)
      |> Option.all in
    let* () =
      Option.some_if
        (List.exists classified ~f:(function
          | `Sliced _ -> true
          | `Invariant _ -> false))
        () in
    let args' =
      List.map classified ~f:(function `Invariant e | `Sliced e -> e) in
    let* () =
      match
        Frontend.Typechecker.stan_math_return_type name
          (List.map ~f:Expr.Typed.fun_arg args')
      with
      | Some (ReturnType UReal) -> Some ()
      | _ -> None in
    let adlevel =
      if UnsizedType.any_autodiff (List.map ~f:Expr.Typed.adlevel_of args') then
        UnsizedType.AutoDiffable
      else DataOnly in
    Some
      (Stmt.Pattern.TargetPE
         Expr.
           { pattern= FunApp (StanLib (name, suffix, mem), args')
           ; meta= {e.meta with adlevel} }) in
  let vectorize_statement sizes = function
    | Stmt.Pattern.For {loopvar; lower; upper; body} as s ->
        Option.value
          (vectorize_for sizes ~loopvar ~lower ~upper body)
          ~default:s
    | s -> s in
  transform_program_blockwise mir (fun fd ->
      let sizes =
        match fd with Some _ -> String.Map.empty | None -> trusted_sizes in
      top_down_map_rec_stmt_loc (vectorize_statement sizes))

(* ================================================================== *)
(* The gathered-families REGISTRY (W-108 increment 2 + W-115).          *)
(*                                                                      *)
(* One table-driven suite pass recognizes the Stan shapes whose         *)
(* gathered operands stan-math has landed specialized primitives for    *)
(* (see [Middle.Gathered_families] for the table itself, and the         *)
(* gathered-GLM campaign records for the bit-identity gates each         *)
(* primitive shipped with) and rewrites them — in the reverse-mode log   *)
(* prob only, so the double-mode instantiation keeps the stock           *)
(* expression (every primitive requires var operands) — into a call to   *)
(* the primitive, which takes the index vectors instead of the gathered  *)
(* matrices and is bit-identical to the composed stock expression while  *)
(* deleting the whole gathered eltwise/loop complex.                     *)
(*                                                                      *)
(* Each entry below is one family:                                       *)
(*   - entry 1, expression class: [y ~ bernoulli_logit(alpha[ii] .*      *)
(*     (theta[jj] - beta[ii]))] (the W-108 increment-2 pass, unchanged); *)
(*   - entry 2, expression class: [-(0.5) * dot_self(phi[node1] -        *)
(*     phi[node2])] — the gathered ICAR prior (W-113); the rewrite only   *)
(*     replaces the [dot_self] call, everything wrapping it (the -0.5,   *)
(*     the target +=) stays untouched;                                   *)
(*   - entry 3, LOOP class (the new matcher class, W-112): the           *)
(*     stereotyped likelihood loop                                       *)
(*     [for (n in 1:N) { mu[n] = alpha[ii[n]] [+ x[n] * beta[ii2[n]]];   *)
(*     target += normal_lpdf(y[n] | mu[n], sigma) }] with [mu]           *)
(*     loop-local, every index expression depending only on [n], and     *)
(*     [sigma] loop-invariant.                                           *)
(*                                                                      *)
(* Every matcher is conservative: any doubt (an extra statement in the   *)
(* loop body, a read of [mu] outside it, a write to [y], a non-data      *)
(* bound, an index expression that is not exactly [idx[n]], a different   *)
(* density head) means NO rewrite. The C++ backend emits the matching    *)
(* [#include] (and, for the per-observation families, the per-term       *)
(* accumulator push loop) only when a rewrite actually fired, so         *)
(* pattern-free models keep their exact generated code.                  *)
(* ================================================================== *)

(* Context every matcher works against: the program's data variables, for
   the index-vector admissibility checks (an index vector must be data so
   the primitive can read it as ints at runtime), and the data variables'
   SIZED types (the loop-class matchers must verify the loop bound is the
   declared length of every data vector the primitive consumes whole). *)
type gathered_ctx =
  { data_vars: String.Set.t
  ; input_sizes: Expr.Typed.t SizedType.t String.Map.t }

let gathered_ctx_of (mir : Program.Typed.t) =
  let data_vars =
    List.map mir.input_vars ~f:(fun (name, _, _) -> name)
    |> String.Set.of_list in
  let input_sizes =
    List.map mir.input_vars ~f:(fun (name, _, ty) -> (name, ty))
    |> String.Map.of_list in
  {data_vars; input_sizes}

(* A gathered coefficient leaf: vector_var [ MultiIndex (data int vector
   var) ]. Returns the bare container var expression, the index variable's
   name, and the bare index var expression. *)
let var_name (e : Expr.Typed.t) : string =
  match e.pattern with Var v -> v | _ -> ""

let gathered_leaf (ctx : gathered_ctx) (e : Expr.Typed.t) :
    (Expr.Typed.t * string * Expr.Typed.t) option =
  match e.pattern with
  | Indexed
      ( ( { pattern= Var _
          ; meta= {type_= UVector; adlevel= AutoDiffable; _}
          ; _ } as container )
      , [ Index.MultiIndex
            ( { pattern= Var idx
              ; meta= {type_= UArray UInt; adlevel= DataOnly; _}
              ; _ } as index ) ] )
    when String.Set.mem idx ctx.data_vars ->
      Some (container, idx, index)
  | _ -> None

(* ------------------------------------------------------------------ *)
(* Entry 1 — the gathered 2PL Bernoulli-logit likelihood (W-108 i2).    *)
(* ------------------------------------------------------------------ *)

(* The IRT likelihood [y ~ bernoulli_logit(alpha[ii] .* (theta[jj] -
   beta[ii]))] lowers in the reverse-mode log prob to

   [bernoulli_logit_lpmf(y, elt_multiply(rvalue(alpha, index_multi(ii)),
   subtract(rvalue(theta, index_multi(jj)), rvalue(beta,
   index_multi(ii)))))]

   which stan-math evaluates through per-elementwise-op autodiff nodes that
   each materialize the gathered operands (the W-34/W-48 measurements: the
   gathered eltwise complex is ~35% of the model's gradient instruction
   count). The paired stan-math primitive

   [bernoulli_logit_lpmf_gathered(y, theta, jj, alpha, beta, ii)]

   takes the index vectors instead of the gathered matrices and is
   bit-identical to the composed stock expression while removing the whole
   complex (-40.9% Ir/grad on hier_2pl, W-108 gate (c)). It accepts the
   operand-mix layouts the compiler actually emits ([var_value] SoA and
   [Matrix<var>] AoS alike), so the rewrite needs no layout side
   conditions. Gates: the density must be [bernoulli_logit_lpmf] whose
   random variable is a data integer vector; the second argument must be
   the literal three-leaf tree [elt_multiply(gather(alpha, ii),
   subtract(gather(theta, jj), gather(beta, ii)))] over AutoDiffable
   vector variables multi-indexed by data integer index vectors, with
   [alpha] and [beta] gathered through the SAME index variable. *)
let bernoulli_logit_statement (ctx : gathered_ctx) p =
  let leaf = gathered_leaf ctx in
  (* The random variable: a data integer vector. *)
  let rv_ok (e : Expr.Typed.t) =
    match (e.pattern, e.meta) with
    | Var _, {type_= UArray UInt; adlevel= DataOnly; _} -> true
    | _ -> false in
  (* Match elt_multiply(gather(a, i), subtract(gather(t, j), gather(b,
     i))) — the exact 2PL predictor shape — and return (theta, jj, alpha,
     beta, ii) in the primitive's parameter order. *)
  let eta_parts (e : Expr.Typed.t) :
      (Expr.Typed.t * Expr.Typed.t * Expr.Typed.t * Expr.Typed.t *
       Expr.Typed.t)
      option =
    match e.pattern with
    | FunApp
        ( StanLib ("EltTimes__", FnPlain, _)
        , [ a
          ; { Expr.pattern=
                FunApp (StanLib ("Minus__", FnPlain, _), [t; b])
            ; _ } ] )
      when (match e.meta with
           | {type_= UVector; adlevel= AutoDiffable; _} -> true
           | _ -> false)
           && (match a.meta with {type_= UVector; _} -> true | _ -> false)
           && (match t.meta with {type_= UVector; _} -> true | _ -> false)
           && (match b.meta with {type_= UVector; _} -> true | _ -> false)
      -> (
        match (leaf a, leaf t, leaf b) with
        | Some (alpha, ix1, ii), Some (theta, _jx, jj), Some (beta, ix2, _)
          when String.equal ix1 ix2 ->
            Some (theta, jj, alpha, beta, ii)
        | _ -> None)
    | _ -> None in
  match p with
  | Stmt.Pattern.TargetPE
      ( { Expr.pattern=
            FunApp (StanLib (name, (FnLpmf _ as suffix), mem), [rv; eta])
        ; _ } as e )
    when String.equal name "bernoulli_logit_lpmf" && rv_ok rv -> (
      match eta_parts eta with
      | Some (theta, jj, alpha, beta, ii) ->
          Stmt.Pattern.TargetPE
            Expr.
              { e with
                pattern=
                  FunApp
                    (StanLib (name ^ "_gathered", suffix, mem)
                    ,[rv; theta; jj; alpha; beta; ii]) }
      | None -> p)
  | _ -> p

(* ------------------------------------------------------------------ *)
(* Entry 2 — the gathered ICAR prior, dot_self (W-113).                 *)
(* ------------------------------------------------------------------ *)

(* The BYM2 ICAR line [target += -0.5 * dot_self(phi[node1] - phi[node2])]
   lowers to [Times__(-0.5, dot_self(Minus__(rvalue(phi, index_multi
   (node1)), rvalue(phi, index_multi(node2)))))]. The primitive
   [dot_self_gathered_diff(phi, node1, node2)] replaces exactly the
   [dot_self] call over a difference of two gathers of the SAME
   AutoDiffable vector through data integer index vectors; the -0.5 and
   whatever else wraps the call are left untouched, and the operand layout
   is left to the C++ overload set (the primitive is bit-exact on all three
   layouts the compiler emits, W-113 gate (a)). *)
let dot_self_gathered_diff_expr (ctx : gathered_ctx) (e : Expr.Typed.t) :
    Expr.Typed.t =
  match e.pattern with
  | FunApp
      ( StanLib ("dot_self", FnPlain, mem)
      , [ { Expr.pattern=
              FunApp (StanLib ("Minus__", FnPlain, _), [a; b])
          ; _ } ] )
    when (match e.meta with
         | {type_= UReal; adlevel= AutoDiffable; _} -> true
         | _ -> false)
         && (match a.meta with {type_= UVector; _} -> true | _ -> false)
         && (match b.meta with {type_= UVector; _} -> true | _ -> false) -> (
      match (gathered_leaf ctx a, gathered_leaf ctx b) with
      | Some (g1, _, i1), Some (g2, _, i2)
        when String.equal (var_name g1) (var_name g2) ->
          Expr.
            { e with
              pattern=
                FunApp
                  ( StanLib ("dot_self_gathered_diff", FnPlain, mem)
                  , [g1; i1; i2] ) }
      | _ -> e)
  | _ -> e

(* Rewrite every subexpression of every statement in the list, bottom-up. *)
let rec dot_self_rewrite_stmt (ctx : gathered_ctx) (s : Stmt.Located.t) :
    Stmt.Located.t =
  let rec go_expr (e : Expr.Typed.t) : Expr.Typed.t =
    let children_mapped =
      Expr.{e with pattern= Expr.Pattern.map go_expr e.pattern} in
    dot_self_gathered_diff_expr ctx children_mapped in
  let go_pattern (p : (Expr.Typed.t, Stmt.Located.t) Stmt.Pattern.t) =
    Stmt.Pattern.map go_expr (dot_self_rewrite_stmt ctx) p in
  {s with pattern= go_pattern s.pattern}

(* ------------------------------------------------------------------ *)
(* Entry 3 — the loop-form normal likelihood (W-112), the LOOP class.   *)
(* ------------------------------------------------------------------ *)

(* The matched shape, exactly as the reverse-mode log prob of

     vector[N] mu;
     for (n in 1:N) {
       mu[n] = alpha[ii[n]];                     // shape A
       mu[n] = alpha[ii[n]] + x[n] * beta[ii2[n]];  // shape B
       target += normal_lpdf(y[n] | mu[n], sigma);
     }

   lowers (shape B appears both as the plain mul-add and, once the O1
   multiply-add fusion has run, as [fma(x[n], beta[ii2[n]], alpha[ii[n]])]).
   The primitive

     normal_lpdf_gathered<propto>(y, alpha, ii [, x, beta, ii2], sigma)

   returns ONE VAR PER OBSERVATION (the accumulator<var> chunk-collapse
   buffer forces that, W-112 §2), so the generated model pushes each term
   into [lp_accum__] in n order — the backend emits that loop; here we only
   replace the whole [for] statement with the primitive's [target +=] call
   and delete the now-unused [mu] declaration (replaced by a [Skip] that
   keeps the statement-numbering labels stable). *)

(* A coefficient leaf indexed by the loop variable: <coef>[<idx>[n]]. *)
let normal_coef_leaf (ctx : gathered_ctx) n (e : Expr.Typed.t) :
    (Expr.Typed.t * Expr.Typed.t) option =
  match e.pattern with
  | Indexed
      ( ( { pattern= Var _
          ; meta= {type_= UVector; adlevel= AutoDiffable; _}
          ; _ } as coef )
      , [ Index.Single
            { Expr.pattern=
                Indexed
                  ( ( { pattern= Var idx
                      ; meta= {type_= UArray UInt; adlevel= DataOnly; _}
                      ; _ } as index )
                  , [Index.Single {pattern= Var nv; _}] )
            ; _ } ] )
    when String.equal nv n && String.Set.mem idx ctx.data_vars ->
      Some (coef, index)
  | _ -> None

(* A data-vector leaf indexed by the loop variable: x[n]. *)
let normal_x_leaf (ctx : gathered_ctx) n (e : Expr.Typed.t) :
    Expr.Typed.t option =
  match e.pattern with
  | Indexed
      ( ( { pattern= Var x
          ; meta= {type_= UVector; adlevel= DataOnly; _}
          ; _ } as xv )
      , [Index.Single {pattern= Var nv; _}] )
    when String.equal nv n && String.Set.mem x ctx.data_vars ->
      Some xv
  | _ -> None

type normal_eta =
  | EtaIntercept of Expr.Typed.t * Expr.Typed.t  (* alpha, ii *)
  | EtaSlope of Expr.Typed.t * Expr.Typed.t * Expr.Typed.t * Expr.Typed.t
                 * Expr.Typed.t  (* alpha, ii, x, beta, ii2 *)

let normal_eta (ctx : gathered_ctx) n (e : Expr.Typed.t) : normal_eta option
    =
  let slope a x b =
    match
      (normal_coef_leaf ctx n a, normal_x_leaf ctx n x, normal_coef_leaf ctx n b)
    with
    | Some (alpha, ii), Some xv, Some (beta, ii2) ->
        Some (EtaSlope (alpha, ii, xv, beta, ii2))
    | _ -> None in
  match e.pattern with
  | (* the fused O1 form: fma(x[n], beta[ii2[n]], alpha[ii[n]]) *)
    FunApp (StanLib ("fma", FnPlain, _), [x; b; a]) -> slope a x b
  | (* the unfused form: alpha[ii[n]] + x[n] * beta[ii2[n]] *)
    FunApp
      ( StanLib ("Plus__", FnPlain, _)
      , [ a
        ; { Expr.pattern=
              FunApp (StanLib ("Times__", FnPlain, _), [x; b])
          ; _ } ] )
    -> slope a x b
  | _ -> (
      match normal_coef_leaf ctx n e with
      | Some (alpha, ii) -> Some (EtaIntercept (alpha, ii))
      | None -> None)

type normal_loop =
  { nl_mu: string  (* the loop-local linear predictor *)
  ; nl_y: Expr.Typed.t  (* the data random-variable container *)
  ; nl_eta: normal_eta
  ; nl_sigma: Expr.Typed.t  (* loop-invariant scale *)
  ; nl_suffix: bool Fun_kind.suffix
  ; nl_mem: Mem_pattern.t
  ; nl_tpe: Expr.Typed.t  (* the matched TargetPE expression *)
  ; nl_meta_asg: Stmt.Located.Meta.t  (* the loop's assignment statement *)
  ; nl_meta_tpe: Stmt.Located.Meta.t  (* the loop's density statement *)
  ; nl_meta_block: Stmt.Located.Meta.t  (* the loop's body block *)
  }

(* Every variable name read inside an expression. *)
let rec expr_var_names (acc : string list ref) (e : Expr.Typed.t) =
  (match e.pattern with Var v -> acc := v :: !acc | _ -> ());
  ignore (Expr.Pattern.map (expr_var_names acc) e.pattern)

let index_exprs (i : Expr.Typed.t Index.t) : Expr.Typed.t list =
  match i with
  | All -> []
  | Single e | Upfrom e | MultiIndex e -> [e]
  | Between (a, b) -> [a; b]

(* Every variable name read or written by a statement (lvalue bases
   included; declarations are not occurrences). *)
let rec stmt_var_names (acc : string list ref) (s : Stmt.Located.t) =
  let rec go_lvalue ((lb, idcs) : Expr.Typed.t Stmt.Pattern.lvalue) =
    (match lb with
    | LVariable v -> acc := v :: !acc
    | LTupleProjection (lv, _) -> go_lvalue lv);
    List.iter
      ~f:(fun i -> List.iter ~f:(expr_var_names acc) (index_exprs i))
      idcs in
  (match s.pattern with
  | Assignment (lv, _, _) -> go_lvalue lv
  | _ -> ());
  ignore
    (Stmt.Pattern.map
       (fun e -> expr_var_names acc e; e)
       (fun x -> stmt_var_names acc x; x)
       s.pattern)

let vars_of_stmts (stmts : Stmt.Located.t list) : string list =
  let acc = ref [] in
  List.iter ~f:(stmt_var_names acc) stmts;
  !acc

(* The lvalue bases this statement writes to (recursively). *)
let rec stmt_written_vars (acc : string list ref) (s : Stmt.Located.t) =
  let rec go_lvalue ((lb, _) : Expr.Typed.t Stmt.Pattern.lvalue) =
    (match lb with
    | LVariable v -> acc := v :: !acc
    | LTupleProjection (lv, _) -> go_lvalue lv) in
  (match s.pattern with
  | Assignment (lv, _, _) -> go_lvalue lv
  | _ -> ());
  ignore
    (Stmt.Pattern.map
       Fun.id
       (fun x -> stmt_written_vars acc x; x)
       s.pattern)

let written_vars_of_stmts (stmts : Stmt.Located.t list) : string list =
  let acc = ref [] in
  List.iter ~f:(stmt_written_vars acc) stmts;
  !acc

(* Does [s] mention the variable [v] (read or write), looking through nested
   statements, but treating [skip1], [skip2] and everything inside them as
   invisible? Used for the loop matcher's "[mu] is mentioned nowhere else"
   side condition, where the skipped statements are the matched loop itself
   and its [mu] declaration — both of which do mention [mu] by
   construction. *)
let rec stmt_mentions_var_skipping (v : string) (skip1 : Stmt.Located.t)
    (skip2 : Stmt.Located.t) (s : Stmt.Located.t) : bool =
  if s == skip1 || s == skip2 then false
  else
    let acc = ref false in
    let rec go_expr (e : Expr.Typed.t) =
      (match e.pattern with
      | Var x when String.equal x v -> acc := true
      | _ -> ());
      if not !acc then ignore (Expr.Pattern.map go_expr e.pattern) in
    let rec go_lvalue ((lb, idcs) : Expr.Typed.t Stmt.Pattern.lvalue) =
      (match lb with
      | LVariable x -> if String.equal x v then acc := true
      | LTupleProjection (lv, _) -> go_lvalue lv);
      if not !acc then
        List.iter ~f:(fun i -> List.iter ~f:go_expr (index_exprs i)) idcs in
    let go_stmt (x : Stmt.Located.t) =
      (if (not !acc) && stmt_mentions_var_skipping v skip1 skip2 x then
         acc := true);
      x in
    (match s.pattern with
    | Assignment (lv, _, rhs) ->
        go_lvalue lv;
        if not !acc then go_expr rhs
    | _ -> ());
    if !acc then true
    else (
      ignore (Stmt.Pattern.map go_expr go_stmt s.pattern);
      !acc)

(* Match the [for] statement itself; the whole-program side conditions
   ([mu] loop-local and otherwise unused, [y] never written) are checked by
   the caller, which sees the whole reverse-mode log prob. *)
let match_normal_loop (ctx : gathered_ctx)
    (pat : (Expr.Typed.t, Stmt.Located.t) Stmt.Pattern.t) :
    normal_loop option =
  match pat with
  | For
      { loopvar= n
      ; lower= {Expr.pattern= Lit (Int, "1"); _}
      ; upper= {meta= {type_= UInt; adlevel= DataOnly; _}; _}
      ; body=
          ( { pattern=
                Block
                  [ ( { pattern=
                          Assignment
                            ( (LVariable mu, [Index.Single {pattern= Var nv; _}])
                            , _
                            , ({meta= {type_= UReal; adlevel= AutoDiffable; _}; _}
                              as eta) )
                      ; meta= m_asg } )
                  ; { pattern=
                        TargetPE
                          ( { Expr.pattern=
                                FunApp
                                  ( StanLib (name, (FnLpdf _ as suffix), mem)
                                  , [y_n; mu_n; sigma] )
                            ; _ } as tpe )
                    ; meta= m_tpe } ]
            ; meta= m_block } as body ) }
    when String.equal nv n && String.equal name "normal_lpdf" -> (
      ignore body;
      let y_ok =
        match y_n.pattern with
        | Indexed
            ( ( { pattern= Var y
                ; meta= {type_= UVector; adlevel= DataOnly; _}
                ; _ } as yv )
            , [Index.Single {pattern= Var ny; _}] )
          when String.equal ny n && String.Set.mem y ctx.data_vars ->
            Some yv
        | _ -> None in
      let mu_ok =
        match mu_n.pattern with
        | Indexed
            ( { pattern= Var mv
              ; meta= {type_= UVector; adlevel= AutoDiffable; _}
              ; _ }
            , [Index.Single {pattern= Var nm; _}] )
          when String.equal nm n && String.equal mv mu ->
            Some ()
        | _ -> None in
      let sigma_ok =
        let names = ref [] in
        expr_var_names names sigma;
        (match sigma.meta with
        | {type_= UReal; _} -> true | _ -> false)
        && not
             (List.exists !names ~f:(fun v ->
                  String.equal v n || String.equal v mu)) in
      match (y_ok, mu_ok, sigma_ok, normal_eta ctx n eta) with
      | Some y, Some (), true, Some e ->
          Some
            { nl_mu= mu
            ; nl_y= y
            ; nl_eta= e
            ; nl_sigma= sigma
            ; nl_suffix= suffix
            ; nl_mem= mem
            ; nl_tpe= tpe
            ; nl_meta_asg= m_asg
            ; nl_meta_tpe= m_tpe
            ; nl_meta_block= m_block }
      | _ -> None)
  | _ -> None

(* Rewrite one matched loop into the primitive's [target +=] call.

   The [for] is replaced by an [SList] of no-op [Skip]s carrying the loop's
   interior statement locations plus the [target +=] call carrying the
   [for]'s own location: the backend's statement numbering registers every
   statement location in traversal order, so this keeps the labels (and
   therefore every printed [current_statement__] number and the whole
   [locations_array__]) EXACTLY what the un-rewritten program would have
   printed, while emitting only the call. *)
let rewrite_normal_loop (m : normal_loop) (for_stmt : Stmt.Located.t) :
    Stmt.Located.t =
  let args =
    match m.nl_eta with
    | EtaIntercept (alpha, ii) -> [m.nl_y; alpha; ii; m.nl_sigma]
    | EtaSlope (alpha, ii, x, beta, ii2) ->
        [m.nl_y; alpha; ii; x; beta; ii2; m.nl_sigma] in
  let call =
    Expr.
      { m.nl_tpe with
        pattern=
          FunApp (StanLib ("normal_lpdf_gathered", m.nl_suffix, m.nl_mem), args)
      } in
  { for_stmt with
    pattern=
      Stmt.Pattern.SList
      [ {pattern= Stmt.Pattern.Skip; meta= m.nl_meta_asg}
      ; {pattern= Stmt.Pattern.Skip; meta= m.nl_meta_tpe}
      ; {pattern= Stmt.Pattern.Skip; meta= m.nl_meta_block}
      ; {pattern= Stmt.Pattern.TargetPE call; meta= for_stmt.meta} ] }

(* One entry's statement-list rewriter: match the loops, check the
   whole-program side conditions, replace the [for] with the call and the
   [mu] declaration with a no-op [Skip] that keeps the location labels (and
   therefore every printed [current_statement__] number) unchanged.

   Side conditions, all of which must hold or nothing fires: [y] is never
   written anywhere in the reverse-mode log prob; [mu] has exactly one
   declaration (a sibling of the loop in the same statement list) and is
   mentioned NOWHERE else in the whole reverse-mode log prob outside that
   declaration and the loop itself. *)
let normal_loops_rewrite (ctx : gathered_ctx) (prog : Stmt.Located.t list) :
    Stmt.Located.t list =
  let written = written_vars_of_stmts prog in
  let y_writable y = List.exists written ~f:(String.equal y) in
  let mentions_outside mu for_stmt decl_stmt =
    List.exists prog ~f:(stmt_mentions_var_skipping mu for_stmt decl_stmt) in
  let is_mu_decl mu (s : Stmt.Located.t) =
    match s.pattern with
    | Decl {decl_id; initialize; _} -> (
        match initialize with
        | Default | Uninit -> String.equal decl_id mu
        | Assign _ -> false)
    | _ -> false in
  (* Fire once in this list: find the first [for] that matches and whose
     [mu] declaration is a sibling in the same statement list. *)
  let fire (l : Stmt.Located.t list) :
      (Stmt.Located.t list * Stmt.Located.t) option =
    let fired = ref None in
    let l' =
      List.map l ~f:(fun (s : Stmt.Located.t) ->
          if Option.is_some !fired then s
          else
            let matched = match_normal_loop ctx s.pattern in
            (match matched with
            | Some m when not (y_writable (var_name m.nl_y)) -> (
                let decls = List.filter l ~f:(is_mu_decl m.nl_mu) in
                match decls with
                | [d]
                  when not (mentions_outside m.nl_mu s d)
                       && List.for_all
                            ~f:(fun x ->
                              let names = vars_of_stmts [x] in
                              not (List.exists names ~f:(String.equal m.nl_mu)))
                            (List.filter l ~f:(fun x ->
                                 not (is_mu_decl m.nl_mu x) && not (x == s)))
                    ->
                    fired := Some d;
                    rewrite_normal_loop m s
                | _ -> s)
            | _ -> s)) in
    match !fired with Some d -> Some (l', d) | None -> None in
  (* Fire repeatedly (a model may have several such loops) and recurse into
     nested blocks. *)
  let rec rewrite_stmt (s : Stmt.Located.t) : Stmt.Located.t =
    match s.pattern with
    | Block l -> {s with pattern= Block (rewrite_list l)}
    | SList l -> {s with pattern= SList (rewrite_list l)}
    | For f ->
        let body' = rewrite_stmt f.body in
        {s with pattern= For {f with body= body'}}
    | IfElse (c, t, e) ->
        let e' = Option.map ~f:rewrite_stmt e in
        {s with pattern= IfElse (c, rewrite_stmt t, e')}
    | While (c, b) -> {s with pattern= While (c, rewrite_stmt b)}
    | Profile (nm, ls) ->
        {s with pattern= Profile (nm, List.map ~f:rewrite_stmt ls)}
    | _ -> s
  and rewrite_list l =
    (* Try to fire on the ORIGINAL statements of this list first: [fire]'s
       whole-program side conditions identify the matched loop and its [mu]
       declaration by physical equality against the untouched program. *)
    match fire l with
    | Some (l', d) ->
        rewrite_list
          (List.map l' ~f:(fun s ->
               if s == d then {s with pattern= Stmt.Pattern.Skip} else s))
    | None -> List.map ~f:rewrite_stmt l in
  rewrite_list prog

(* ------------------------------------------------------------------ *)
(* Entry 4 — the composed USER-FUNCTION pcm likelihood (W-126/W-132),  *)
(* the through-the-inlined-function matcher class.                      *)
(* ------------------------------------------------------------------ *)

(* The gpcm/ordered-Irt likelihood is not a library density: the model
   defines

     real pcm(int y, real theta, vector beta) {
       vector[rows(beta) + 1] unsummed;
       vector[rows(beta) + 1] probs;
       unsummed = append_row(rep_vector(0.0, 1), theta - beta);
       probs = softmax(cumulative_sum(unsummed));
       return categorical_lpmf(y + 1 | probs);
     }

   and calls it per observation:

     for (n in 1:N)
       target += pcm(y[n], theta[jj[n]] .* alpha[ii[n]],
                     segment(beta, pos[ii[n]], m[ii[n]]));

   At --O1 [function_inlining] — the FIRST pass of the suite — expands the
   call, so by the time [gathered_families] (the LAST pass) runs, the loop
   body is the inlined body with the call-site arguments substituted:

     { Decl ret;
       { FnValidateSize; Decl unsummed; FnValidateSize; Decl probs;
         unsummed = append_row(rep_vector(0, 1),
                               Minus__(theta[jj[n]] * alpha[ii[n]],
                                       segment(beta, pos[ii[n]], m[ii[n]])));
         probs = softmax(cumulative_sum(unsummed));
         ret = categorical_lpmf(y[n] + 1 | probs); }
       target += ret; }

   Matching THROUGH the user function is therefore a matter of matching this
   stereotyped inlined statement sequence (the W-131 lesson: the pattern is
   EASIER post-inlining — the body is fully visible and the fresh
   [inline_pcm_*] locals cannot be mentioned outside the loop). The paired
   primitive

     pcm_lpdf_gathered<propto>(y, theta, jj, alpha, ii, beta, pos, m)

   (W-126, math#23) consumes the index vectors and the item tables instead
   of the per-observation expressions and is bit-identical to the composed
   stock path while deleting its whole per-observation expression complex
   (-88.3% Ir on the gate model). It returns one var per observation (the
   W-112 accumulator contract). *)

(* A gathered SCALAR read through the loop variable: coef[idx[n]] — the
   container an AutoDiffable vector, the index a data int array read at
   [n]. Returns (container, index container, index name). *)
let pcm_scalar_gather (ctx : gathered_ctx) n (e : Expr.Typed.t) :
    (Expr.Typed.t * Expr.Typed.t * string) option =
  match e.pattern with
  | Indexed
      ( ( { pattern= Var _
          ; meta= {type_= UVector; adlevel= AutoDiffable; _}
          ; _ } as container )
      , [ Index.Single
            { Expr.pattern=
                Indexed
                  ( ( { pattern= Var idx
                      ; meta= {type_= UArray UInt; adlevel= DataOnly; _}
                      ; _ } as index )
                  , [Index.Single {pattern= Var nv; _}] )
            ; _ } ] )
    when String.equal nv n && String.Set.mem idx ctx.data_vars ->
      Some (container, index, idx)
  | _ -> None

(* The gathered bilinear theta[jj[n]] .* alpha[ii[n]] — both spellings of
   the scalar product ([.* ] eltwise and [*] plain) decompose to the same
   two gathered scalars; returns them in the expression's own order. *)
let pcm_bilinear (ctx : gathered_ctx) n (e : Expr.Typed.t) :
    (Expr.Typed.t * Expr.Typed.t * string * Expr.Typed.t * Expr.Typed.t * string)
    option =
  match e.pattern with
  | FunApp
      ( StanLib (("EltTimes__" | "Times__"), FnPlain, _)
      , [a; b] )
    when (match e.meta with
          | {type_= UReal; adlevel= AutoDiffable; _} -> true
          | _ -> false) -> (
      match (pcm_scalar_gather ctx n a, pcm_scalar_gather ctx n b) with
      | Some (t, tj, tix), Some (a', aj, aix) ->
          Some (t, tj, tix, a', aj, aix)
      | _ -> None)
  | _ -> None

(* An item-table read through the observation's item index: tbl[ii[n]] —
   the table a data int array, the index the SAME [ii] the bilinear's
   alpha operand is gathered through. *)
let pcm_item_table (_ctx : gathered_ctx) n ii (e : Expr.Typed.t) :
    Expr.Typed.t option =
  match e.pattern with
  | Indexed
      ( ( { pattern= Var _
          ; meta= {type_= UArray UInt; adlevel= DataOnly; _}
          ; _ } as container )
      , [ Index.Single
            { Expr.pattern=
                Indexed
                  ( { pattern= Var idx
                    ; meta= {type_= UArray UInt; adlevel= DataOnly; _}
                    ; _ }
                  , [Index.Single {pattern= Var nv; _}] )
            ; _ } ] )
    when String.equal nv n && String.equal idx ii ->
      Some container
  | _ -> None

(* segment(beta, pos[ii[n]], m[ii[n]]) — the concatenated-steps window for
   the observation's item. *)
let pcm_segment (ctx : gathered_ctx) n ii (e : Expr.Typed.t) :
    (Expr.Typed.t * Expr.Typed.t * Expr.Typed.t) option =
  match e.pattern with
  | FunApp
      ( StanLib ("segment", FnPlain, _)
      , [ ( { pattern= Var _
            ; meta= {type_= UVector; adlevel= AutoDiffable; _}
            ; _ } as beta )
        ; start
        ; len ] ) -> (
      match (pcm_item_table ctx n ii start, pcm_item_table ctx n ii len) with
      | Some pos, Some m -> Some (beta, pos, m)
      | _ -> None)
  | _ -> None

let pcm_zero_literal (e : Expr.Typed.t) : bool =
  match e.pattern with
  | Lit (Real, "0.0") | Lit (Int, "0") -> true
  | Promotion ({pattern= Lit (Int, "0"); _}, _, _) -> true
  | _ -> false

type pcm_loop =
  { pl_bound: string  (* the loop upper bound (a data variable) *)
  ; pl_y: Expr.Typed.t  (* the data response container *)
  ; pl_theta: Expr.Typed.t
  ; pl_jj: Expr.Typed.t
  ; pl_alpha: Expr.Typed.t
  ; pl_ii: Expr.Typed.t
  ; pl_beta: Expr.Typed.t
  ; pl_pos: Expr.Typed.t
  ; pl_m: Expr.Typed.t
  ; pl_tpe: Expr.Typed.t  (* the matched categorical_lpmf expr *)
  ; pl_mem: Mem_pattern.t
  ; pl_metas: Stmt.Located.Meta.t list  (* interior statements, post-order *)
  }

(* Match the [for] statement itself. The whole-program side conditions
   (loop bound = the declared length of [y]/[jj]/[ii]; [y] never written)
   are checked by the caller, which sees the whole reverse-mode log prob
   and the program's data block. *)
let match_pcm_loop (ctx : gathered_ctx)
    (pat : (Expr.Typed.t, Stmt.Located.t) Stmt.Pattern.t) : pcm_loop option =
  match pat with
  | For
      { loopvar= n
      ; lower= {Expr.pattern= Lit (Int, "1"); _}
      ; upper= {Expr.pattern= Var bound; meta= {type_= UInt; adlevel= DataOnly; _}; _}
      ; body=
          ( { pattern=
                Block
                  [ ( { pattern= Decl {decl_id= ret; _}
                      ; meta= m_ret } )
                  ; ( { pattern=
                          Block
                            [ ( { pattern=
                                  NRFunApp (CompilerInternal FnValidateSize, _)
                                ; meta= m_val1 } )
                            ; ({pattern= Decl {decl_id= u; _}; meta= m_decl_u})
                            ; ( { pattern=
                                  NRFunApp (CompilerInternal FnValidateSize, _)
                                ; meta= m_val2 } )
                            ; ({pattern= Decl {decl_id= p; _}; meta= m_decl_p})
                            ; ( { pattern=
                                    Assignment
                                      ((LVariable ua, []), _, rhs_u)
                                ; meta= m_asn_u } )
                            ; ( { pattern=
                                    Assignment ((LVariable pa, []), _, rhs_p)
                                ; meta= m_asn_p } )
                            ; ( { pattern=
                                    Assignment ((LVariable ra, []), _, rhs_l)
                                ; meta= m_asn_r } ) ]
                      ; meta= m_inner } as inner )
                  ; ( { pattern= TargetPE {Expr.pattern= Var rt; _}
                      ; meta= m_tpe } ) ]
            ; meta= m_body } ) }
    when String.equal ua u && String.equal pa p && String.equal ra ret
         && String.equal rt ret
         && String.Set.mem bound ctx.data_vars -> (
      (* probs = softmax(cumulative_sum(unsummed)) *)
      let probs_ok =
        match rhs_p.pattern with
        | FunApp
            ( StanLib ("softmax", FnPlain, _)
            , [ { Expr.pattern=
                    FunApp
                      (StanLib ("cumulative_sum", FnPlain, _), [pu])
                ; _ } ] )
          when (match rhs_p.meta with
                | {type_= UVector; adlevel= AutoDiffable; _} -> true
                | _ -> false) -> (
            match pu.Expr.pattern with
            | Var pu' -> String.equal pu' u
            | _ -> false)
        | _ -> false in
      (* ret = categorical_lpmf(y[n] + 1 | probs) *)
      let lpmf_parts =
        match rhs_l.pattern with
        | FunApp
            ( StanLib ("categorical_lpmf", (FnLpmf _ as suffix), mem)
            , [ { Expr.pattern=
                    FunApp
                      (StanLib ("Plus__", FnPlain, _), [y_n; {pattern= Lit (Int, "1"); _}])
                ; _ }
              ; {pattern= Var lp; _} ] ) -> (
            match y_n.Expr.pattern with
            | Indexed
                ( ( { pattern= Var _
                    ; meta= {type_= UArray UInt; adlevel= DataOnly; _}
                    ; _ } as yv )
                , [Index.Single {pattern= Var ny; _}] )
              when String.equal ny n && String.Set.mem (var_name yv) ctx.data_vars
                   && String.equal lp p ->
                Some (yv, suffix, mem)
            | _ -> None)
        | _ -> None in
      (* unsummed = append_row(rep_vector(0, 1), bilinear - segment) *)
      let unsummed_parts =
        match rhs_u.pattern with
        | FunApp
            ( StanLib ("append_row", FnPlain, _)
            , [ { Expr.pattern=
                    FunApp
                      ( StanLib ("rep_vector", FnPlain, _)
                      , [z; {pattern= Lit (Int, "1"); _}] )
                ; _ }
              ; { Expr.pattern=
                    FunApp (StanLib ("Minus__", FnPlain, _), [bil; seg])
                ; _ } ] )
          when pcm_zero_literal z
               && (match rhs_u.meta with
                   | {type_= UVector; adlevel= AutoDiffable; _} -> true
                   | _ -> false) -> (
            match pcm_bilinear ctx n bil with
            | Some (t, tj, tix, a, aj, aix) -> (
                (* The segment's item index picks out which bilinear operand
                   is the ITEM side (alpha): it must be gathered through the
                   same index the segment windows the item tables with. The
                   other operand is then the person side (theta) — either
                   source spelling (theta[jj] .* alpha[ii] or commuted)
                   decomposes to the primitive's (theta, jj, alpha, ii) with
                   BOTH bindings swapped together, never a mix (the operand
                   mix-up would silently drop a container — the W-115 §6
                   lesson). *)
                match pcm_segment ctx n aix seg with
                | Some (beta, pos, m) -> Some (t, tj, a, aj, beta, pos, m)
                | None -> (
                    match pcm_segment ctx n tix seg with
                    | Some (beta, pos, m) -> Some (a, aj, t, tj, beta, pos, m)
                    | None -> None))
            | None -> None)
        | _ -> None in
      match (probs_ok, lpmf_parts, unsummed_parts) with
      | true, Some (yv, suffix, mem), Some (theta, jj, alpha, ii, beta, pos, m)
        when suffix = FnLpmf false || suffix = FnLpmf true -> (
          ignore inner;
          Some
            { pl_bound= bound
            ; pl_y= yv
            ; pl_theta= theta
            ; pl_jj= jj
            ; pl_alpha= alpha
            ; pl_ii= ii
            ; pl_beta= beta
            ; pl_pos= pos
            ; pl_m= m
            ; pl_tpe= rhs_l
            ; pl_mem= mem
            ; pl_metas=
                [ m_ret; m_val1; m_decl_u; m_val2; m_decl_p; m_asn_u
                ; m_asn_p; m_asn_r; m_inner; m_tpe; m_body ] })
      | _ -> None)
  | _ -> None

(* Rewrite one matched loop into the primitive's [target +=] call: the
   [for] becomes an [SList] of no-op [Skip]s carrying every interior
   statement location (in the numbering pass's post-order, so the whole
   [locations_array__] stays EXACTLY what the un-rewritten program prints)
   plus the call carrying the [for]'s own location — the entry-3
   convention. The primitive's [<propto__>] template argument is inert
   (the pcm interior has no constant terms, W-126 header doc), matching
   the gated hand-edit's spelling. *)
let rewrite_pcm_loop (m : pcm_loop) (for_stmt : Stmt.Located.t) :
    Stmt.Located.t =
  let call =
    Expr.
      { m.pl_tpe with
        pattern=
          FunApp
            ( StanLib ("pcm_lpdf_gathered", FnLpmf true, m.pl_mem)
            , [ m.pl_y; m.pl_theta; m.pl_jj; m.pl_alpha; m.pl_ii
              ; m.pl_beta; m.pl_pos; m.pl_m ] ) } in
  { for_stmt with
    pattern=
      Stmt.Pattern.SList
        ( List.map m.pl_metas
            ~f:(fun meta ->
              ({pattern= Stmt.Pattern.Skip; meta} : Stmt.Located.t))
        @ [ {pattern= Stmt.Pattern.TargetPE call; meta= for_stmt.meta} ] ) }

(* One entry's statement-list rewriter: match the loops, check the
   whole-program side conditions, replace the [for] with the call.

   Side conditions, all of which must hold or nothing fires: the loop
   bound is a bare data variable that is ALSO the declared length of
   [y], [jj] and [ii] (the primitive consumes all four whole, so the
   stock loop must have processed exactly the containers' full extent);
   [y] is never written anywhere in the reverse-mode log prob. The
   loop-local [inline_pcm_*] variables are gensym-fresh and declared
   inside the loop, so they cannot be mentioned elsewhere. *)
let pcm_loops_rewrite (ctx : gathered_ctx) (prog : Stmt.Located.t list) :
    Stmt.Located.t list =
  let written = written_vars_of_stmts prog in
  let sized_array_of_bound bound name =
    match String.Map.find_opt name ctx.input_sizes with
    | Some (SizedType.SArray (SInt, {Expr.pattern= Var sz; _})) ->
        String.equal sz bound
    | _ -> false in
  let side_ok (m : pcm_loop) =
    (not (List.exists written ~f:(fun v -> String.equal v (var_name m.pl_y))))
    && sized_array_of_bound m.pl_bound (var_name m.pl_y)
    && sized_array_of_bound m.pl_bound (var_name m.pl_jj)
    && sized_array_of_bound m.pl_bound (var_name m.pl_ii) in
  let fire (l : Stmt.Located.t list) : Stmt.Located.t list option =
    let fired = ref false in
    let l' =
      List.map l ~f:(fun (s : Stmt.Located.t) ->
          if !fired then s
          else
            match match_pcm_loop ctx s.pattern with
            | Some m when side_ok m ->
                fired := true;
                rewrite_pcm_loop m s
            | _ -> s) in
    if !fired then Some l' else None in
  let rec rewrite_stmt (s : Stmt.Located.t) : Stmt.Located.t =
    match s.pattern with
    | Block l -> {s with pattern= Block (rewrite_list l)}
    | SList l -> {s with pattern= SList (rewrite_list l)}
    | For f ->
        let body' = rewrite_stmt f.body in
        {s with pattern= For {f with body= body'}}
    | IfElse (c, t, e) ->
        let e' = Option.map ~f:rewrite_stmt e in
        {s with pattern= IfElse (c, rewrite_stmt t, e')}
    | While (c, b) -> {s with pattern= While (c, rewrite_stmt b)}
    | Profile (nm, ls) ->
        {s with pattern= Profile (nm, List.map ~f:rewrite_stmt ls)}
    | _ -> s
  and rewrite_list l =
    match fire l with
    | Some l' -> rewrite_list l'
    | None -> List.map ~f:rewrite_stmt l
  in
  rewrite_list prog

(* The registry: one row per landed family, in emission order. Each rewrite
   sees the statement list of [reverse_mode_log_prob] only. *)
let gathered_registry :
    (string * (gathered_ctx -> Stmt.Located.t list -> Stmt.Located.t list))
    list =
  [ ( "bernoulli_logit_lpmf_gathered"
    , fun ctx stmts ->
        List.map stmts ~f:(map_rec_stmt_loc (bernoulli_logit_statement ctx))
    )
  ; ( "dot_self_gathered_diff"
    , fun ctx stmts -> List.map stmts ~f:(dot_self_rewrite_stmt ctx) )
  ; ("normal_lpdf_gathered", normal_loops_rewrite)
  ; ("pcm_lpdf_gathered", pcm_loops_rewrite) ]

(* The suite pass: apply every registered family to the reverse-mode log
   prob. *)
let gathered_families (mir : Program.Typed.t) =
  let ctx = gathered_ctx_of mir in
  let prog =
    List.fold_left gathered_registry ~init:mir.reverse_mode_log_prob
      ~f:(fun stmts (_, rewrite) -> rewrite ctx stmts) in
  {mir with reverse_mode_log_prob= prog}

let collapse_lists_statement _ =
  let rec collapse_lists l =
    match l with
    | [] -> []
    | Stmt.{pattern= SList l'; _} :: rest -> l' @ collapse_lists rest
    | x :: rest -> x :: collapse_lists rest in
  let f = function
    | Stmt.Pattern.Block l -> Stmt.Pattern.Block (collapse_lists l)
    | SList l -> SList (collapse_lists l)
    | x -> x in
  map_rec_stmt_loc f

let list_collapsing (mir : Program.Typed.t) =
  transform_program_blockwise mir collapse_lists_statement

let propagation
    (propagation_transfer :
         Stmt.Located.Non_recursive.t LabelMap.t
      -> (module Monotone_framework_sigs.TRANSFER_FUNCTION
            with type labels = int
             and type properties = Middle.Expr.Typed.t String.Map.t option))
    (mir : Program.Typed.t) =
  let transform stmt =
    let flowgraph, flowgraph_to_mir =
      Monotone_framework.forward_flowgraph_of_stmt stmt in
    let (module Flowgraph) = flowgraph in
    let values =
      Monotone_framework.propagation_mfp mir
        (module Flowgraph)
        flowgraph_to_mir propagation_transfer in
    let propagate_stmt =
      map_rec_stmt_loc_num flowgraph_to_mir (fun i ->
          subst_stmt_base
            (Option.value ~default:String.Map.empty
               (LabelMap.find i values).entry)) in
    propagate_stmt (LabelMap.find 1 flowgraph_to_mir) in
  transform_program mir transform

let constant_propagation ?(preserve_stability = false) =
  propagation
    (Monotone_framework.constant_propagation_transfer ~preserve_stability)

let expression_propagation ?(preserve_stability = false) mir =
  propagation
    (Monotone_framework.expression_propagation_transfer ~preserve_stability
       (cannot_duplicate_expr ~preserve_stability))
    mir

let copy_propagation mir =
  let globals = Monotone_framework.globals mir in
  propagation (Monotone_framework.copy_propagation_transfer globals) mir

let is_skip_break_continue s =
  match s with Stmt.Pattern.Skip | Break | Continue -> true | _ -> false

(* TODO: could also implement partial dead code elimination *)
let dead_code_elimination (mir : Program.Typed.t) =
  (* TODO: think about whether we should treat function bodies as local scopes
     in the statement from the POV of a live variables analysis. (Obviously,
     this shouldn't be the case for the purposes of reaching definitions,
     constant propagation, expressions analyses. But I do think that's the right
     way to go about live variables. *)
  let transform s =
    let rev_flowgraph, flowgraph_to_mir =
      Monotone_framework.inverse_flowgraph_of_stmt s in
    let (module Rev_Flowgraph) = rev_flowgraph in
    let live_variables =
      Monotone_framework.live_variables_mfp mir
        (module Rev_Flowgraph)
        flowgraph_to_mir in
    let dead_code_elim_stmt_base i stmt =
      (* NOTE: entry in the reverse flowgraph, so exit in the forward
         flowgraph *)
      let live_variables_s =
        (LabelMap.find i live_variables).Monotone_framework_sigs.entry in
      match stmt with
      | Stmt.Pattern.Assignment (lhs, _, rhs) ->
          if
            Set.Poly.mem (Middle.Stmt.Helpers.lhs_variable lhs) live_variables_s
            || cannot_remove_expr rhs
            || List.exists
                 ~f:(idx_any cannot_remove_expr)
                 (Middle.Stmt.Helpers.lhs_indices lhs)
          then stmt
          else Skip
      (* NOTE: we never get rid of declarations as we might not be able to
         remove an assignment to a variable
            due to side effects. *)
      (* TODO: maybe we should revisit that. *)
      | Decl ({decl_id; initialize= Assign e; _} as decl) ->
          if Set.Poly.mem decl_id live_variables_s || cannot_remove_expr e then
            stmt
          else Decl {decl with initialize= Uninit}
      | Decl _ | TargetPE _ | JacobianPE _
       |NRFunApp (_, _)
       |Break | Continue | Return _ | Skip ->
          stmt
      | IfElse (e, b1, b2) -> (
          if
            (* TODO: check if e has side effects, like print, reject, then don't
               optimize? *)
            (not (cannot_remove_expr e))
            && b1.Stmt.pattern = Skip
            && (Option.map ~f:(fun Stmt.{pattern; _} -> pattern) b2 = Some Skip
               || Option.map ~f:(fun Stmt.{pattern; _} -> pattern) b2 = None)
          then Skip
          else
            match e.pattern with
            | _ when Partial_evaluator.is_int 0 e -> (
                match b2 with Some x -> x.pattern | None -> Skip)
            | Lit (_, _) -> b1.pattern
            | _ -> IfElse (e, b1, b2))
      | While (e, b) -> (
          if (not (cannot_remove_expr e)) && b.pattern = Break then Skip
          else
            match e.pattern with
            | _ when Partial_evaluator.is_int 0 e -> Skip
            | _ -> While (e, b))
      | For {loopvar; lower; upper; body} ->
          if
            (not (cannot_remove_expr lower))
            && (not (cannot_remove_expr upper))
            && is_skip_break_continue body.pattern
          then Skip
          else For {loopvar; lower; upper; body}
      | Profile (name, l) ->
          let l' = List.filter ~f:(fun x -> x.Stmt.pattern <> Skip) l in
          if List.is_empty l' then Skip else Profile (name, l')
      | Block l ->
          let l' = List.filter ~f:(fun x -> x.Stmt.pattern <> Skip) l in
          if List.is_empty l' then Skip else Block l'
      | SList l ->
          let l' = List.filter ~f:(fun x -> x.Stmt.pattern <> Skip) l in
          SList l' in
    let dead_code_elim_stmt =
      map_rec_stmt_loc_num flowgraph_to_mir dead_code_elim_stmt_base in
    dead_code_elim_stmt (LabelMap.find 1 flowgraph_to_mir) in
  transform_program mir transform

let partial_evaluation = Partial_evaluator.eval_prog

(** Given a name and Stmt, search the statement for the first assignment where
    that name is the assignee. *)
let rec find_assignment_idx (name : string) Stmt.{pattern; _} =
  match pattern with
  | Stmt.Pattern.Assignment (lval, lhs_ut, (rhs : 'a Expr.t)) ->
      let assign_name = Stmt.Helpers.lhs_variable lval in
      let idx_lst = Stmt.Helpers.lhs_indices lval in
      if
        name = assign_name
        && (not (Set.Poly.mem assign_name (expr_var_names_set rhs)))
        && not
             (rhs.meta.adlevel = UnsizedType.DataOnly
             && UnsizedType.is_array lhs_ut)
      then Some idx_lst
      else None
  | _ -> None

(** Given a list of Stmts, find Decls whose objects are fully assigned to in
    their first assignment and mark them as not needing to be initialized. *)
and unenforce_initialize (lst : Stmt.Located.t list) =
  let rec unenforce_initialize_patt (Stmt.{pattern; _} as stmt) sub_lst =
    match pattern with
    | Stmt.Pattern.Decl ({decl_id; initialize= Default; _} as decl_pat) -> (
        match List.hd sub_lst with
        | Some next_stmt -> (
            match find_assignment_idx decl_id next_stmt with
            | Some idxs when Index.every_index_is_all idxs ->
                { stmt with
                  pattern= Stmt.Pattern.Decl {decl_pat with initialize= Uninit}
                }
            | None | Some _ -> stmt)
        | None -> stmt)
    | Block block_lst ->
        {stmt with pattern= Block (unenforce_initialize block_lst)}
    | SList s_lst -> {stmt with pattern= SList (unenforce_initialize s_lst)}
    (*[] here because we do not want to check out of scope *)
    | While (expr, stmt) ->
        {stmt with pattern= While (expr, unenforce_initialize_patt stmt [])}
    | For ({body; _} as pat) ->
        { stmt with
          pattern= For {pat with body= unenforce_initialize_patt body []} }
    | Profile ((pname : string), stmts) ->
        {stmt with pattern= Profile (pname, unenforce_initialize stmts)}
    | IfElse ((expr : 'a Expr.t), true_stmt, op_false_stmt) ->
        let mod_false_stmt =
          Option.map ~f:(fun x -> unenforce_initialize_patt x []) op_false_stmt
        in
        { stmt with
          pattern=
            IfElse (expr, unenforce_initialize_patt true_stmt [], mod_false_stmt)
        }
    | _ -> stmt in
  match List.hd lst with
  | Some stmt -> (
      match List.tl lst with
      | Some sub_lst ->
          List.cons
            (unenforce_initialize_patt stmt sub_lst)
            (unenforce_initialize sub_lst)
      | None -> lst)
  | None -> lst

(** Take the Mir and perform a transform that requires searching across the list
    inside of each piece of the Mir.
    @param mir The mir
    @param transformer a function that takes in and returns a list of Stmts. *)
let transform_mir_blocks (mir : Program.Typed.t)
    (transformer : Stmt.Located.t list -> Stmt.Located.t list) : Program.Typed.t
    =
  let transformed_functions =
    List.map mir.functions_block ~f:(fun fs ->
        let new_body =
          match fs.Program.fdbody with
          | Some (Stmt.{pattern= SList lst; _} as stmt) ->
              Some {stmt with pattern= SList (transformer lst)}
          | Some (Stmt.{pattern= Block lst; _} as stmt) ->
              Some {stmt with pattern= Block (transformer lst)}
          | alt -> alt in
        {fs with fdbody= new_body}) in
  { Program.functions_block= transformed_functions
  ; input_vars= mir.input_vars
  ; prepare_data= transformer mir.prepare_data
  ; log_prob= transformer mir.log_prob
  ; reverse_mode_log_prob= transformer mir.reverse_mode_log_prob
  ; generate_quantities= transformer mir.generate_quantities
  ; transform_inits= transformer mir.transform_inits
  ; unconstrain_array= transformer mir.unconstrain_array
  ; output_vars= mir.output_vars
  ; prog_name= mir.prog_name
  ; prog_path= mir.prog_path }

let allow_uninitialized_decls mir =
  transform_mir_blocks mir unenforce_initialize

let lazy_code_motion ?(preserve_stability = false) (mir : Program.Typed.t) =
  (* TODO: clean up this code. It is not very pretty. *)
  (* TODO: make lazy code motion operate on transformed parameters and models blocks
     simultaneously *)
  let preprocess_flowgraph =
    let preprocess_flowgraph_base
        (stmt : (Expr.Typed.t, Stmt.Located.t) Stmt.Pattern.t) =
      match stmt with
      | IfElse (e, b1, Some b2) ->
          Stmt.(
            Pattern.IfElse
              ( e
              , { pattern= Block [b1; {pattern= Skip; meta= Location_span.empty}]
                ; meta= Location_span.empty }
              , Some
                  { pattern=
                      Block [b2; {pattern= Skip; meta= Location_span.empty}]
                  ; meta= Location_span.empty } ))
      | IfElse (e, b, None) ->
          IfElse
            ( e
            , { pattern= Block [b; {pattern= Skip; meta= Location_span.empty}]
              ; meta= Location_span.empty }
            , Some {pattern= Skip; meta= Location_span.empty} )
      | While (e, b) ->
          While
            ( e
            , { pattern= Block [b; {pattern= Skip; meta= Location_span.empty}]
              ; meta= Location_span.empty } )
      | For {loopvar; lower; upper; body= b} ->
          For
            { loopvar
            ; lower
            ; upper
            ; body=
                { pattern= Block [b; {pattern= Skip; meta= Location_span.empty}]
                ; meta= Location_span.empty } }
      | _ -> stmt in
    map_rec_stmt_loc preprocess_flowgraph_base in
  let transform s =
    let rev_flowgraph, flowgraph_to_mir =
      Monotone_framework.inverse_flowgraph_of_stmt ~blocks_after_body:false s
    in
    let fwd_flowgraph = Monotone_framework.reverse rev_flowgraph in
    let latest_expr, used_not_latest_expressions_mfp =
      Monotone_framework.lazy_expressions_mfp fwd_flowgraph rev_flowgraph
        flowgraph_to_mir in
    let expression_map =
      let rec collect_expressions accum (e : Expr.Typed.t) =
        match e.pattern with
        | Lit (_, _) -> accum
        | Var _ -> accum
        | _ when cannot_duplicate_expr ~preserve_stability e ->
            (* Immovable expressions might have movable subexpressions *)
            Expr.Pattern.fold collect_expressions accum e.pattern
        | _ ->
            ExprMap.add accum ~key:e ~data:(Gensym.generate ~prefix:"lcm_" ())
      in
      ExprSet.fold
        (Monotone_framework.used_expressions_stmt s.pattern)
        ~init:ExprMap.empty
        ~f:(Fun.flip collect_expressions) in
    (* TODO: it'd be more efficient to just not accumulate constants in the
       static analysis *)
    let declarations_list =
      ExprMap.fold expression_map ~init:[] ~f:(fun ~key ~data accum ->
          Stmt.
            { pattern=
                Pattern.Decl
                  { decl_adtype= Expr.Typed.adlevel_of key
                  ; decl_id= data
                  ; decl_type= Type.Unsized (Expr.Typed.type_of key)
                  ; initialize= Default }
            ; meta= Location_span.empty }
          :: accum) in
    let lazy_code_motion_base i stmt =
      let latest_and_used_after_i =
        ExprSet.inter
          (LabelMap.find i latest_expr)
          (LabelMap.find i used_not_latest_expressions_mfp).entry in
      let to_assign_in_s =
        latest_and_used_after_i
        |> ExprSet.filter ~f:(fun x -> ExprMap.mem x expression_map)
        |> ExprSet.to_list
        |> List.sort ~cmp:(fun e e' ->
            Int.compare (expr_depth e) (expr_depth e')) in
      (* TODO: is this sort doing anything or are they already stored in the
         right order by chance? It appears to not do anything. *)
      let assignments_to_add_to_s =
        List.map
          ~f:(fun e ->
            Stmt.
              { pattern=
                  Assignment
                    ( Stmt.Helpers.lvariable (ExprMap.find e expression_map)
                    , e.meta.type_
                    , e )
              ; meta= Location_span.empty })
          to_assign_in_s in
      let expr_subst_stmt_except_initial_assign m =
        let f stmt =
          match stmt with
          | Stmt.Pattern.Assignment ((LVariable x, []), _, e')
           |Decl {decl_id= x; initialize= Assign e'; _}
            when ExprMap.mem e' m
                 && Expr.Typed.equal {e' with pattern= Var x}
                      (ExprMap.find e' m) ->
              expr_subst_stmt_base (ExprMap.remove e' m) stmt
          | _ -> expr_subst_stmt_base m stmt in
        map_rec_stmt_loc f in
      let expr_map =
        ExprMap.filter
          ~f:(fun key _ ->
            ExprSet.mem key latest_and_used_after_i
            || ExprSet.mem key
                 (LabelMap.find i used_not_latest_expressions_mfp).exit)
          (ExprMap.mapi expression_map ~f:(fun key data ->
               {key with pattern= Var data})) in
      let f = expr_subst_stmt_except_initial_assign expr_map in
      if List.is_empty assignments_to_add_to_s then
        (f Stmt.{pattern= stmt; meta= Location_span.empty}).pattern
      else
        SList
          (List.map ~f
             (assignments_to_add_to_s
             @ [{pattern= stmt; meta= Location_span.empty}])) in
    let lazy_code_motion_stmt =
      map_rec_stmt_loc_num flowgraph_to_mir lazy_code_motion_base in
    Stmt.
      { pattern=
          SList
            (declarations_list
            @ [lazy_code_motion_stmt (LabelMap.find 1 flowgraph_to_mir)])
      ; meta= Location_span.empty } in
  let cleanup =
    let cleanup_base (stmt : (Expr.Typed.t, Stmt.Located.t) Stmt.Pattern.t) :
        (Expr.Typed.t, Stmt.Located.t) Stmt.Pattern.t =
      match stmt with
      | Stmt.(
          Pattern.IfElse
            ( e
            , {pattern= Block [b1; {pattern= Skip; _}]; _}
            , Some {pattern= Block [b2; {pattern= Skip; _}]; _} )) ->
          IfElse (e, b1, Some b2)
      | IfElse
          ( e
          , {pattern= Block [b; {pattern= Skip; _}]; _}
          , Some {pattern= Skip; _} ) ->
          IfElse (e, b, None)
      | While (e, {pattern= Block [b; {pattern= Skip; _}]; _}) -> While (e, b)
      | For
          { loopvar
          ; lower
          ; upper
          ; body= {pattern= Block [b; {pattern= Skip; _}]; _} } ->
          For {loopvar; lower; upper; body= b}
      | _ -> stmt in
    map_rec_stmt_loc cleanup_base in
  transform_program_blockwise mir (fun _ x ->
      cleanup (transform (preprocess_flowgraph x)))

let block_fixing mir =
  transform_program_blockwise mir (fun _ x ->
      (map_rec_stmt_loc (fun stmt ->
           match stmt with
           | IfElse
               ( e
               , {pattern= SList l; meta}
               , Some {pattern= SList l'; meta= smeta'} ) ->
               IfElse
                 ( e
                 , {pattern= Block l; meta}
                 , Some {pattern= Block l'; meta= smeta'} )
           | IfElse (e, {pattern= SList l; meta}, b) ->
               IfElse (e, {pattern= Block l; meta}, b)
           | IfElse (e, b, Some {pattern= SList l'; meta= smeta'}) ->
               IfElse (e, b, Some {pattern= Block l'; meta= smeta'})
           | While (e, {pattern= SList l; meta}) ->
               While (e, {pattern= Block l; meta})
           | For {loopvar; lower; upper; body= {pattern= SList l; meta}} ->
               For {loopvar; lower; upper; body= {pattern= Block l; meta}}
           | _ -> stmt))
        x)

(* TODO: implement SlicStan style optimizer for choosing best program block for each statement. *)
(* TODO: add optimization pass to move declarations down as much as possible and introduce as
   tight as possible local scopes *)
(* TODO: add tests *)
(* TODO: add pass to get rid of redundant declarations? *)

(** A generic optimization pass for finding a minimal set of variables that are
    generated by some circumstance, and then updating the MIR with that set.
    @param gen_variables:
      the variables that must be added to the set at the given statement
    @param update_expr: update an MIR expression given the variable set
    @param update_stmt:
      Function for updating an MIR statement given the variable set
    @param extra_variables:
      the set of variables that are implied to be in the set by a given variable
      in the set (usually empty, sometimes unrepresented variables like _in__
      variables)
    @param initial_variables: the initial known members of the set of variables
    @param stmt the MIR statement to optimize. *)
let optimize_minimal_variables
    ~(gen_variables :
          Stmt.Located.Non_recursive.t LabelMap.t
       -> int
       -> string Set.Poly.t
       -> string Set.Poly.t)
    ~(update_expr : string Set.Poly.t -> Expr.Typed.t -> Expr.Typed.t)
    ~(update_stmt :
          (Expr.Typed.t, (Expr.Typed.Meta.t, 'a) Stmt.t) Stmt.Pattern.t
       -> string Set.Poly.t
       -> (Expr.Typed.t, (Expr.Typed.Meta.t, 'a) Stmt.t) Stmt.Pattern.t)
    ~(extra_variables : string -> string Set.Poly.t)
    ~(initial_variables : string Set.Poly.t) (stmt : Stmt.Located.t) =
  let rev_flowgraph, flowgraph_to_mir =
    Monotone_framework.inverse_flowgraph_of_stmt stmt in
  let fwd_flowgraph = Monotone_framework.reverse rev_flowgraph in
  let (module Circular_Fwd_Flowgraph) =
    Monotone_framework.make_circular_flowgraph fwd_flowgraph rev_flowgraph in
  let mfp_variables =
    Monotone_framework.minimal_variables_mfp
      (module Circular_Fwd_Flowgraph)
      flowgraph_to_mir initial_variables gen_variables in
  let optimize_min_vars_stmt_base i stmt_pattern =
    let variable_set =
      let exits = (LabelMap.find i mfp_variables).exit in
      Set.Poly.union exits (Set.Poly.union_map exits ~f:extra_variables) in
    let stmt_val =
      Stmt.Pattern.map (update_expr variable_set) (fun x -> x) stmt_pattern
    in
    update_stmt stmt_val variable_set in
  map_rec_stmt_loc_num flowgraph_to_mir optimize_min_vars_stmt_base
    (LabelMap.find 1 flowgraph_to_mir)

(* XXX: This optimization current promotes/demotes entire tuples at once. This
   could be significantly better *)
let optimize_ad_levels (mir : Program.Typed.t) =
  let gen_ad_variables
      (flowgraph_to_mir : Stmt.Located.Non_recursive.t LabelMap.t) (l : int)
      (ad_variables : string Set.Poly.t) =
    let mir_node = (LabelMap.find l flowgraph_to_mir).pattern in
    match mir_node with
    | Assignment (lval, _, e)
      when UnsizedType.is_autodifftype
           @@ Expr.Typed.adlevel_of (update_expr_ad_levels ad_variables e) ->
        Set.Poly.singleton (Stmt.Helpers.lhs_variable lval)
    | _ -> Set.Poly.empty in
  let global_initial_ad_variables =
    Set.Poly.of_list
      (List.filter_map
         ~f:(fun (v, _, Program.{out_block; _}) ->
           match out_block with Parameters -> Some v | _ -> None)
         mir.output_vars) in
  let initial_ad_variables fundef_opt _ =
    match (fundef_opt : Stmt.Located.t Program.fun_def option) with
    | None -> global_initial_ad_variables
    | Some {fdargs; _} ->
        Set.Poly.union global_initial_ad_variables
          (Set.Poly.of_list
             (List.filter_map fdargs ~f:(fun (_, name, ut) ->
                  if UnsizedType.is_autodiffable ut then Some name else None)))
  in
  let extra_variables v = Set.Poly.singleton (v ^ "_in__") in
  let update_stmt stmt_pattern variable_set =
    match stmt_pattern with
    | Stmt.Pattern.Decl ({decl_id; decl_type; _} as decl)
      when Set.Poly.mem decl_id variable_set ->
        Stmt.Pattern.Decl
          { decl with
            decl_adtype=
              UnsizedType.fill_adtype_for_type UnsizedType.AutoDiffable
                (Type.to_unsized decl_type) }
    | Decl ({decl_id; decl_type; _} as decl)
      when not (Set.Poly.mem decl_id variable_set) ->
        Decl
          { decl with
            decl_adtype=
              UnsizedType.fill_adtype_for_type UnsizedType.DataOnly
                (Type.to_unsized decl_type) }
    | s -> s in
  let transform fundef_opt stmt =
    optimize_minimal_variables ~gen_variables:gen_ad_variables
      ~update_expr:update_expr_ad_levels ~update_stmt ~extra_variables
      ~initial_variables:(initial_ad_variables fundef_opt stmt)
      stmt in
  transform_program_blockwise mir transform

(** Deduces whether types can be Structures of Arrays (SoA/fast) or Arrays of
    Structs (AoS/slow). See the docs in Mem_pattern.query_demote_stmt/exprs*
    functions for details on the rules surrounding when demotion from SoA -> AoS
    needs to happen.

    This first does a simple iter over the log_prob portion of the MIR, finding
    the names of all matrices (and arrays of matrices) where either the Stan
    math function does not support SoA or the object is single cell accessed
    within a For or While loop. These are the initial variables given to the
    monotone framework. Then log_prob has all matrix like objects and the
    functions that use them to SoA. After that the Monotone framework is used to
    deduce assignment paths of AoS <-> SoA and vice versa which need to be
    demoted to AoS as well as updating functions and objects after these
    assignment passes that then also need to be AoS.

    @param mir: The program's whole MIR. *)
let optimize_soa (mir : Program.Typed.t) =
  let gen_aos_variables
      (flowgraph_to_mir : Stmt.Located.Non_recursive.t LabelMap.t) (l : int)
      (aos_variables : string Set.Poly.t) =
    let mir_node mir_idx = LabelMap.find mir_idx flowgraph_to_mir in
    Memory_patterns.query_demotable_stmt aos_variables (mir_node l) in
  let initial_variables =
    List.fold_left ~init:Set.Poly.empty
      ~f:(Memory_patterns.query_initial_demotable_stmt false)
      mir.reverse_mode_log_prob in
  let mod_exprs aos_exits mod_expr =
    Mir_utils.map_rec_expr
      (Memory_patterns.modify_expr_pattern aos_exits)
      mod_expr in
  let modify_stmt_patt stmt_pattern variable_set =
    Memory_patterns.modify_stmt_pattern stmt_pattern variable_set in
  let transform stmt =
    optimize_minimal_variables ~gen_variables:gen_aos_variables
      ~update_expr:mod_exprs ~update_stmt:modify_stmt_patt ~initial_variables
      stmt ~extra_variables:(fun _ -> initial_variables) in
  let transform' s =
    match transform {pattern= SList s; meta= Location_span.empty} with
    | {pattern= SList (l : Stmt.Located.t list); _} -> l
    | _ ->
        ICE.internal_error
          "Something went wrong with program transformation packing!"
        [@coverage off] in
  {mir with reverse_mode_log_prob= transform' mir.reverse_mode_log_prob}

(* Apparently you need to completely copy/paste type definitions between ml and
   mli files?*)
type optimization_settings =
  { function_inlining: bool
  ; static_loop_unrolling: bool
  ; one_step_loop_unrolling: bool
  ; vectorize_loops: bool
  ; list_collapsing: bool
  ; block_fixing: bool
  ; allow_uninitialized_decls: bool
  ; constant_propagation: bool
  ; expression_propagation: bool
  ; copy_propagation: bool
  ; dead_code_elimination: bool
  ; partial_evaluation: bool
  ; lazy_code_motion: bool
  ; optimize_ad_levels: bool
  ; preserve_stability: bool
  ; optimize_soa: bool
  ; gathered_families: bool }

let settings_const b =
  { function_inlining= b
  ; static_loop_unrolling= b
  ; one_step_loop_unrolling= b
  ; vectorize_loops= b
  ; list_collapsing= b
  ; block_fixing= b
  ; allow_uninitialized_decls= b
  ; constant_propagation= b
  ; expression_propagation= b
  ; copy_propagation= b
  ; dead_code_elimination= b
  ; partial_evaluation= b
  ; lazy_code_motion= b
  ; optimize_ad_levels= b
  ; preserve_stability= not b
  ; optimize_soa= b
  ; gathered_families= b }

let all_optimizations : optimization_settings = settings_const true
let no_optimizations : optimization_settings = settings_const false

type optimization_level = O0 | O1 | Oexperimental

let level_optimizations (lvl : optimization_level) : optimization_settings =
  match lvl with
  | O0 -> no_optimizations
  | O1 ->
      { function_inlining= true
      ; static_loop_unrolling= false
      ; one_step_loop_unrolling= false
      ; vectorize_loops= false
      ; list_collapsing= true
      ; block_fixing= true
      ; constant_propagation= true
      ; expression_propagation= false
      ; copy_propagation= true
      ; dead_code_elimination= true
      ; partial_evaluation= true
      ; lazy_code_motion= false
      ; allow_uninitialized_decls= true
      ; optimize_ad_levels= false
      ; preserve_stability= false
      ; optimize_soa= true
      ; gathered_families= true }
  | Oexperimental -> all_optimizations

let optimization_suite ?(settings = all_optimizations) mir =
  let preserve_stability = settings.preserve_stability in
  let maybe_optimizations =
    [ (* Phase order. See phase-ordering-nodes.org for details *)
      (* Book section A *)
      (* Book section B *)
      (* Book: Procedure integration *)
      (function_inlining, settings.function_inlining)
      (* Book: Sparse conditional constant propagation *)
    ; (constant_propagation ~preserve_stability, settings.constant_propagation)
      (* Book section C *)
      (* Book: Local and global copy propagation *)
    ; (copy_propagation, settings.copy_propagation)
      (* Book: Sparse conditional constant propagation *)
    ; (constant_propagation ~preserve_stability, settings.constant_propagation)
      (* Book: Dead-code elimination *)
    ; (dead_code_elimination, settings.dead_code_elimination)
      (* Vectorization needs the loops intact, so it runs before one-step
         unrolling. *)
    ; (vectorize_loops, settings.vectorize_loops)
      (* Matthijs: Before lazy code motion to get loop-invariant code motion *)
    ; (one_step_loop_unrolling, settings.one_step_loop_unrolling)
      (* Matthjis: expression_propagation < partial_evaluation *)
    ; ( expression_propagation ~preserve_stability
      , settings.expression_propagation )
      (* Matthjis: partial_evaluation < lazy_code_motion *)
    ; (partial_evaluation, settings.partial_evaluation)
      (* Book: Loop-invariant code motion *)
    ; (lazy_code_motion ~preserve_stability, settings.lazy_code_motion)
      (* Matthijs: lazy_code_motion < copy_propagation TODO: Check if this is
         necessary *)
    ; (copy_propagation, settings.copy_propagation)
      (* Matthijs: Constant propagation before static loop unrolling *)
    ; (constant_propagation ~preserve_stability, settings.constant_propagation)
      (* Book: Loop simplification *)
    ; (static_loop_unrolling, settings.static_loop_unrolling)
      (* Book: Dead-code elimination *)
      (* Matthijs: Everything < Dead-code elimination *)
    ; (dead_code_elimination, settings.dead_code_elimination)
      (* Book: Machine idioms and instruction combining *)
    ; (list_collapsing, settings.list_collapsing)
      (* Book: Machine idioms and instruction combining *)
    ; (optimize_ad_levels, settings.optimize_ad_levels)
    ; (optimize_soa, settings.optimize_soa)
      (* Remove decls immediately assigned to *)
    ; (allow_uninitialized_decls, settings.allow_uninitialized_decls)
      (* Book: Machine idioms and instruction combining *)
      (* Matthijs: Everything < block_fixing *)
    ; (block_fixing, settings.block_fixing)
      (* The gathered-families registry: rewrites every registered gathered
         Stan shape (bernoulli_logit 2PL, ICAR dot_self, the loop-form
         normal likelihood) into its primitive call; runs LAST so no other
         pass rewrites the calls it produces. *)
    ; (gathered_families, settings.gathered_families) ] in
  let optimizations =
    List.filter_map maybe_optimizations ~f:(fun (fn, flag) ->
        if flag then Some fn else None) in
  List.fold_left optimizations ~init:mir ~f:( |> )
