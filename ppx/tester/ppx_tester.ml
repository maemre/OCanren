(*
 * OCanren. PPX syntax extensions.
 * Copyright (C) 2016-2023
 *   Dmitrii Kosarev aka Kakadu
 * St.Petersburg State University, JetBrains Research
 *)

(**
  An extension that allows not to write errornous qh, qrh and stuff like that.
  It looks at number of lambdas in the last argument, and insert numberals as penultimate argument.

  Expands

    {[ let __ _ = [%tester runR OCanren.reify show_int show_intl (fun q -> q === !!1)] ]}

  to

  {[
    let __ _ =
      runR OCanren.reify show_int show_intl q qh
        ("<string repr of goal>", (fun q -> q === (!! 1)))
  ]}

*)

open Ppxlib

let string_of_expression e =
  Format.set_margin 1000;
  Format.set_max_indent 0;
  let ans = Format.asprintf "%a" Pprintast.expression e in
  ans
;;

let name = "tester"

let () =
  let extensions =
    let pattern =
      let open Ast_pattern in
      pstr
        (pstr_eval
           (pexp_apply
              __
              ((nolabel ** __) ^:: (nolabel ** __) ^:: (nolabel ** __) ^:: (nolabel ** __) ^:: nil))
           nil
        ^:: nil)
    in
    [ Extension.declare
        name
        Extension.Context.Expression
        pattern
        (fun ~loc ~path:_ runner reifier shower n realtion ->
          let open Ppxlib.Ast_builder.Default in
          let count =
            let rec helper acc e =
              match e.pexp_desc with
              | Pexp_fun (_, _, _, body) -> helper (1 + acc) body
              | _ -> acc
            in
            helper 0 realtion
          in
          let middle =
            match count with
            | 0 -> failwith "Bad syntax"
            | 1 -> [ [%expr OCanren.q]; [%expr qh] ]
            | 2 -> [ [%expr OCanren.qr]; [%expr qrh] ]
            | 3 -> [ [%expr OCanren.qrs]; [%expr qrsh] ]
            | 4 -> [ [%expr OCanren.qrst]; [%expr qrsth] ]
            | _ -> failwith (Printf.sprintf "5 and more arguments are not supported")
          in
          let last =
            let s = string_of_expression @@ realtion in
            let open Ppxlib.Ast_builder.Default in
            [%expr [%e pexp_constant ~loc (Pconst_string (s, loc, None))], [%e realtion]]
          in
          pexp_apply ~loc runner
          @@ List.map (fun e -> Nolabel, e)
          @@ List.concat [ [ reifier; shower; n ]; middle; [ last ] ])
    ]
  in
  Ppxlib.Driver.register_transformation ~extensions name
;;
