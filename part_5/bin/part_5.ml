type var = string

type expr =
  | Type
  | Var of var
  | App of expr * expr
  | Abs of var * expr * expr
  | Pi of var * expr * expr
  (* forget about the constructors below at first *)
  | Nat
  | Z
  | S of expr
  | Ind of expr * expr * expr * expr
  | Eq of expr * expr
  | Refl of expr
  | J of expr * expr * expr * expr * expr

type context = (var * (expr * expr option)) list

exception Type_error

let n = ref 0

let fresh_var () =
  incr n;
  "x" ^ string_of_int !n

let rec int_of_expr = function
  | Z -> 0
  | S e -> 1 + int_of_expr e
  | _ -> raise Type_error

let rec to_string = function
  | Type -> "Type"
  | Var a -> a
  | App (f, x) -> "(" ^ to_string f ^ " " ^ to_string x ^ ")"
  | Abs (a, x, y) ->
      "(fun (" ^ a ^ " : " ^ to_string x ^ ") -> " ^ to_string y ^ ")"
  | Pi (a, x, y) -> "((" ^ a ^ " : " ^ to_string x ^ ") -> " ^ to_string y ^ ")"
  | Nat -> "Nat"
  | Z -> "0"
  | S x -> (
      try string_of_int (int_of_expr (S x))
      with Type_error -> "(S " ^ to_string x ^ ")")
  | Ind (typ, zero, hered, n) ->
      "Ind (" ^ to_string typ ^ "," ^ to_string zero ^ "," ^ to_string hered
      ^ "," ^ to_string n ^ ")"
  | Eq (_, _) -> assert false
  | Refl _ -> assert false
  | J (_, _, _, _, _) -> assert false

let rec is_free_variable x = function
  | Type | Nat | Z -> true
  | Var v -> x = v
  | App (a, b) | Abs (_, a, b) | Pi (_, a, b) ->
      is_free_variable x a || is_free_variable x b
  | S a -> is_free_variable x a
  | Ind (typ, zero, hered, n) ->
      is_free_variable x typ || is_free_variable x zero
      || is_free_variable x hered || is_free_variable x n
  | Eq (_, _) -> assert false
  | Refl _ -> assert false
  | J (_, _, _, _, _) -> assert false

(*let rec subst x t = function
  | Type -> Type
  | Var v when v = x -> t
  | Var v -> Var v
  | App (a, b) -> App (subst x t a, subst x t b)
  | Abs (xvar, ty, f) when xvar = x || is_free_variable x f ->
      let v = fresh_var () in
      (* Abs (v, subst v (Var xvar) ty, subst v (Var xvar) f) *)
      Abs
        (v, subst x t (subst xvar (Var v) ty), subst x t (subst xvar (Var v) t))
  | Abs (xvar, ty, f) -> Abs (xvar, subst x t ty, subst x t f)
  | Pi (xvar, ty, f) when xvar = x || is_free_variable x f ->
      let v = fresh_var () in
      Abs
        (v, subst x t (subst xvar (Var v) ty), subst x t (subst xvar (Var v) t))
  | Pi (xvar, ty, f) -> Pi (xvar, subst x t ty, subst x t f)
  | _ -> assert false
*)
let rec subst x u = function
  | Type -> Type
  | Var y when y = x -> u
  | Var y -> Var y
  | App (t, t') -> App (subst x u t, subst x u t')
  | Abs (y, a, t) when y = x || is_free_variable y u ->
      let z = fresh_var () in
      Abs (z, subst x u (subst y (Var z) a), subst x u (subst y (Var z) t))
  | Abs (y, a, t) -> Abs (y, subst x u a, subst x u t)
  | Pi (y, a, b) when y = x || is_free_variable y u ->
      let z = fresh_var () in
      Pi (z, subst x u (subst y (Var z) a), subst x u (subst y (Var z) b))
  | Pi (y, a, b) -> Pi (y, subst x u a, subst x u b)
  | Nat -> Nat
  | Z -> Z
  | S n -> S (subst x u n)
  | Ind (typ, zero, hered, n) ->
      Ind (subst x u typ, subst x u zero, subst x u hered, subst x u n)
  | Eq (_, _) -> assert false
  | Refl _ -> assert false
  | J (_, _, _, _, _) -> assert false

let rec string_of_context = function
  | [] -> ""
  | (x, (ty, None)) :: q ->
      (match q with [] -> "" | _ -> string_of_context q ^ "\n")
      ^ x ^ " : " ^ to_string ty
  | (x, (ty, Some value)) :: q ->
      (match q with [] -> "" | _ -> string_of_context q ^ "\n")
      ^ x ^ " : " ^ to_string ty ^ " = " ^ to_string value

let rec get_type_from_context var = function
  | (x, (typ, _)) :: _ when x = var -> typ
  | _ :: q -> get_type_from_context var q
  | [] -> raise Type_error

let rec get_value_from_context var = function
  | (x, (_, Some value)) :: _ when x = var -> value
  | (x, (_, None)) :: _ when x = var -> raise Type_error
  | _ :: q -> get_value_from_context var q
  | [] -> raise Type_error

let rec nat_to_int = function
  | Z -> 0
  | S n -> 1 + nat_to_int n
  | _ -> raise Type_error

let rec red_aux (env : context) = function
  | Type -> (Type, false)
  | Var v -> (
      try (get_value_from_context v env, true)
      with Type_error -> (Var v, false))
  | App (Abs (x, _, f), y) -> (subst x y f, true)
  | App (x, y) ->
      let x_reduced, x_bool = red_aux env x
      and y_reduced, y_bool = red_aux env y in
      (App (x_reduced, y_reduced), x_bool || y_bool)
  | Abs (x, y, z) ->
      let a, b = red_aux ((x, (y, None)) :: env) z in
      (Abs (x, a, z), b)
  | Pi (x, y, z) ->
      let y_op, y_ch = red_aux env y
      and z_op, z_ch = red_aux ((x, (y, None)) :: env) z in
      (Pi (x, y_op, z_op), y_ch || z_ch)
  | Nat -> (Nat, false)
  | Z -> (Z, false)
  | S n ->
      let n_red, reducded = red_aux env n in
      (S n_red, reducded)
  | Ind (typ, init, hered, n) -> (
      let typ_red, typ_bool = red_aux env typ
      and init_red, init_bool = red_aux env init
      and hered_red, hered_bool = red_aux env hered
      and n_red, n_bool = red_aux env n in
      match n_red with
      | Z -> (init_red, true)
      | S n_red ->
          ( App
              (App (hered_red, n_red), Ind (typ_red, init_red, hered_red, n_red)),
            true )
      | _ ->
          ( Ind (typ_red, init_red, hered_red, n_red),
            typ_bool || init_bool || hered_bool || n_bool ))
  | Eq (_, _) -> assert false
  | Refl _ -> assert false
  | J (_, _, _, _, _) -> assert false

let rec normalize env t =
  match red_aux env t with
  | reduced, true -> normalize env reduced
  | reduced, false -> reduced

let rec alpha = function
  | Type -> ( function Type -> true | _ -> false)
  | Var x -> ( function Var y when x = y -> true | _ -> false)
  | App (f, x) -> (
      function App (f1, x1) -> alpha f f1 && alpha x x1 | _ -> false)
  | Abs (xvar1, ty1, f1) -> (
      function
      | Abs (xvar2, ty2, f2) when xvar1 = xvar2 -> alpha ty1 ty2 && alpha f1 f2
      | Abs (xvar2, ty2, f2) ->
          let xvar = fresh_var () in
          alpha (subst xvar1 (Var xvar) ty1) (subst xvar2 (Var xvar1) ty2)
          && alpha (subst xvar1 (Var xvar) f1) (subst xvar2 (Var xvar1) f2)
      | _ -> false)
  | Pi (xvar1, ty1, f1) -> (
      function
      | Pi (xvar2, ty2, f2) when xvar1 = xvar2 -> alpha ty1 ty2 && alpha f1 f2
      | Pi (xvar2, ty2, f2) ->
          alpha ty1 (subst xvar2 (Var xvar1) ty2)
          && alpha f1 (subst xvar2 (Var xvar1) f2)
      | _ -> false)
  | Nat -> ( function Nat -> true | _ -> false)
  | Z -> ( function Z -> true | _ -> false)
  | S x -> ( function S y -> alpha x y | _ -> false)
  | Ind (typ1, init1, hered1, n1) -> (
      function
      | Ind (typ2, init2, hered2, n2)
        when alpha typ1 typ2 && alpha init1 init2 && alpha hered1 hered2
             && alpha n1 n2 ->
          true
      | _ -> false)
  | Eq (_, _) -> assert false
  | Refl _ -> assert false
  | J (_, _, _, _, _) -> assert false

let conv (env : context) a b =
  (* print_endline "normalized";
     print_endline (to_string (normalize context a));
     print_endline (to_string (normalize context b));
     print_endline "end of normalized"; *)
  alpha (normalize env a) (normalize env b)

let rec infer_aux (env : context) = function
  | Type | Pi (_, _, _) | Nat -> Type
  | Var v -> get_type_from_context v env
  | App (f, x) -> (
      match infer env f with
      | Pi (y, a, b) ->
          let type_x = infer env x in
          if conv ((y, (type_x, Some x)) :: env) a type_x then
            normalize ((y, (type_x, Some x)) :: env) b
          else raise Type_error
      | _ -> raise Type_error)
  | Abs (x, type_x, fx) ->
      print_endline (to_string type_x);
      let type_f = infer ((x, (type_x, None)) :: env) fx in
      Pi (x, type_x, type_f)
  | Z -> Nat
  | S n when infer env n = Nat -> Nat
  | S _ -> raise Type_error
  | Ind (typ, init, hered, n)
    when conv env (infer env init) (App (typ, Z)) && conv env Nat (infer env n)
    ->
      let next_type = App (typ, S n) in
      (* print_endline "infer ind";
         print_endline (to_string next_type);
         print_endline
           (to_string
              (infer env (normalize env (App (App (hered, n), App (typ, n))))));
         print_endline "end infer ind"; *)
      if
        conv env next_type
          (normalize env (infer env (App (App (hered, n), App (typ, n)))))
      then normalize env (App (typ, n))
      else raise Type_error
  | Ind (typ, init, hered, n) ->
      print_endline (to_string (normalize env init));
      print_endline (to_string (normalize env (App (typ, Z))));
      print_endline (to_string n);
      print_endline (string_of_context env);
      print_endline "type of n";
      print_endline (to_string (normalize env (infer env n)));
      raise Type_error
  | Eq (_, _) -> assert false
  | Refl _ -> assert false
  | J (_, _, _, _, _) -> assert false

and infer env expr = infer_aux env expr

let check env exp typ =
  if conv env (infer env exp) typ then () else raise Type_error

(** Parsing of expressions. *)
let () = Printexc.record_backtrace true

exception Parse_error

let lexer =
  Genlex.make_lexer
    [
      "(";
      ",";
      ")";
      "->";
      "=>";
      "fun";
      "Pi";
      ":";
      "Type";
      "Nat";
      "Z";
      "S";
      "Ind";
      "Eq";
      "Refl";
      "J";
    ]

let of_tk s =
  let must_kwd s k =
    match Stream.next s with
    | Genlex.Kwd k' when k' = k -> ()
    | _ -> raise Parse_error
  in
  let peek_kwd s k =
    match Stream.peek s with
    | Some (Genlex.Kwd k') when k' = k ->
        let _ = Stream.next s in
        true
    | _ -> false
  in
  let stream_is_empty s =
    try
      Stream.empty s;
      true
    with Stream.Failure -> false
  in
  let ident s =
    match Stream.next s with Genlex.Ident x -> x | _ -> raise Parse_error
  in
  let noapp =
    List.map
      (fun k -> Some (Genlex.Kwd k))
      [ ")"; "->"; "=>"; "fun"; "Pi"; ":"; "Type" ]
  in
  let rec e () = abs ()
  and abs () =
    if peek_kwd s "Pi" then (
      must_kwd s "(";
      let x = ident s in
      must_kwd s ":";
      let a = e () in
      must_kwd s ")";
      must_kwd s "->";
      let b = e () in
      Pi (x, a, b))
    else if peek_kwd s "fun" then (
      must_kwd s "(";
      let x = ident s in
      must_kwd s ":";
      let a = e () in
      must_kwd s ")";
      must_kwd s "->";
      let t = e () in
      Abs (x, a, t))
    else app ()
  and app () =
    let t = ref (arr ()) in
    while (not (stream_is_empty s)) && not (List.mem (Stream.peek s) noapp) do
      t := App (!t, base ())
    done;
    !t
  and arr () =
    let t = base () in
    if peek_kwd s "=>" then
      let u = e () in
      Pi ("_", t, u)
    else t
  and base () =
    match Stream.next s with
    | Genlex.Ident x -> Var x
    | Genlex.Kwd "Type" -> Type
    | Genlex.Kwd "Nat" -> Nat
    | Genlex.Kwd "Z" -> Z
    | Genlex.Kwd "S" ->
        let t = base () in
        S t
    | Genlex.Kwd "Ind" ->
        let p = base () in
        let z = base () in
        let ps = base () in
        let n = base () in
        Ind (p, z, ps, n)
    | Genlex.Kwd "Eq" ->
        let t = base () in
        let u = base () in
        Eq (t, u)
    | Genlex.Kwd "Refl" ->
        let t = base () in
        Refl t
    | Genlex.Kwd "J" ->
        let p = base () in
        let r = base () in
        let x = base () in
        let y = base () in
        let e = base () in
        J (p, r, x, y, e)
    | Genlex.Kwd "(" ->
        let t = e () in
        must_kwd s ")";
        t
    | _ -> raise Parse_error
  in
  e ()

let of_string a = of_tk (lexer (Stream.of_string a))

let () =
  let env = ref [] in
  let loop = ref true in
  let file = open_out "interactive.proof" in
  let split c s =
    try
      let n = String.index s c in
      ( String.trim (String.sub s 0 n),
        String.trim (String.sub s (n + 1) (String.length s - (n + 1))) )
    with Not_found -> (s, "")
  in
  while !loop do
    try
      print_string "? ";
      flush_all ();
      let cmd, arg =
        let cmd = input_line stdin in
        output_string file (cmd ^ "\n");
        print_endline cmd;
        split ' ' cmd
      in
      match cmd with
      | "assume" ->
          let x, sa = split ':' arg in
          let a = of_string sa in
          check !env a Type;
          env := (x, (a, None)) :: !env;
          print_endline (x ^ " assumed of type " ^ to_string a)
      | "define" ->
          let x, st = split '=' arg in
          let t = of_string st in
          let a = infer !env t in
          env := (x, (a, Some t)) :: !env;
          print_endline
            (x ^ " defined to " ^ to_string t ^ " of type " ^ to_string a)
      | "context" -> print_endline (string_of_context !env)
      | "type" ->
          let t = of_string arg in
          let a = infer !env t in
          print_endline (to_string t ^ " is of type " ^ to_string a)
      | "check" ->
          let t, a = split '=' arg in
          let t = of_string t in
          let a = of_string a in
          check !env t a;
          print_endline "Ok."
      | "eval" ->
          let t = of_string arg in
          let _ = infer !env t in
          print_endline (to_string (normalize !env t))
      | "exit" -> loop := false
      | "" | "#" -> ()
      | cmd -> print_endline ("Unknown command: " ^ cmd)
    with
    | End_of_file -> loop := false
    | Failure err -> print_endline ("Error: " ^ err ^ ".")
    (* | e -> print_endline ("Error: "^Printexc.to_string e) *)
  done;
  print_endline "Bye."
