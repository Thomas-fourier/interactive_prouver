type tvar = string
(** Type variables. *)

type var = string
(** Term variables. *)

type ty =
  | TVar of tvar
  | Imp of ty * ty
  | And of ty * ty
  | Or of ty * ty
  | True
  | False
  | Nat

type tm =
  | Var of var
  | App of tm * tm
  | Abs of var * ty * tm
  | Pair of tm * tm
  | Fst of tm
  | Snd of tm
  | Left of tm * ty
  | Right of ty * tm
  | Case of tm * tm * tm
  | Unit
  | Absurd of tm * ty
  | Zero
  | Suc of tm
  | Rec of tm * tm * tm

type context = (var * ty) list

exception Type_error

let rec nat_to_int = function
  | Zero -> 0
  | Suc n -> 1 + nat_to_int n
  | _ -> raise Type_error

let rec string_of_ty = function
  | TVar t -> t
  | Imp (t1, t2) -> "(" ^ string_of_ty t1 ^ "=>" ^ string_of_ty t2 ^ ")"
  | And (t1, t2) -> "(" ^ string_of_ty t1 ^ "/\\" ^ string_of_ty t2 ^ ")"
  | True -> "T"
  | False -> "_"
  | Or (t1, t2) -> "(" ^ string_of_ty t1 ^ "\\/" ^ string_of_ty t2 ^ ")"
  | Nat -> "Nat"

let rec string_of_tm = function
  | Var t -> t
  | App (t1, t2) -> "(" ^ string_of_tm t1 ^ " " ^ string_of_tm t2 ^ ")"
  | Abs (f, t, exp) ->
      "(fun " ^ f ^ ":" ^ string_of_ty t ^ ") -> " ^ string_of_tm exp
  | Pair (t1, t2) -> "(" ^ string_of_tm t1 ^ " , " ^ string_of_tm t2 ^ ")"
  | Fst t -> "left(" ^ string_of_tm t ^ ")"
  | Snd t -> "right(" ^ string_of_tm t ^ ")"
  | Left (t, _) -> "left(" ^ string_of_tm t ^ ")"
  | Right (_, t) -> "right(" ^ string_of_tm t ^ ")"
  | Case (t1, t2, t3) ->
      "case " ^ string_of_tm t1 ^ " of " ^ string_of_tm t2 ^ " | "
      ^ string_of_tm t3
  | Unit -> "()"
  | Absurd (tm, ty) -> "False " ^ string_of_tm tm ^ "," ^ string_of_ty ty
  | Suc t -> (
      try string_of_int (nat_to_int t + 1)
      with Type_error -> "Suc of " ^ string_of_tm t)
  | Zero -> "0"
  | Rec (n, zero, succ) -> (
      match succ with
      (* here the sectond argument is a function wich takes as input the value of the previous  *)
      | Abs (x, _, fx) -> (
          "Match " ^ string_of_tm n ^ " with \n |0 -> " ^ string_of_tm zero
          ^ "\n |succ " ^ x ^ " -> "
          ^
          match fx with
          | Abs (x, _, fx) ->
              " with " ^ x ^ " = fct evaluated at pred -> " ^ string_of_tm fx
          | _ -> raise Type_error)
      | _ -> raise Type_error)

let rec type_of_var t = function
  | (a, b) :: _ when a = t -> b
  | _ :: q -> type_of_var t q
  | [] -> raise Type_error

let rec infer_type gamma = function
  | Var t -> type_of_var t gamma
  | App (t1, t2) -> (
      match infer_type gamma t1 with
      | Imp (a, b) ->
          check_type gamma t2 a;
          b
      | _ -> raise Type_error)
  | Abs (x, t, expr) -> Imp (t, infer_type ((x, t) :: gamma) expr)
  | Pair (x1, x2) -> And (infer_type gamma x1, infer_type gamma x2)
  | Fst x -> (
      match infer_type gamma x with And (x, _) -> x | _ -> raise Type_error)
  | Snd x -> (
      match infer_type gamma x with And (_, x) -> x | _ -> raise Type_error)
  | Unit -> True
  | Left (t1, t2) -> Or (infer_type gamma t1, t2)
  | Right (t1, t2) -> Or (t1, infer_type gamma t2)
  | Case (t1, t2, t3) -> (
      match infer_type gamma t1 with
      | Or (x1, x2) -> (
          match (infer_type gamma t2, infer_type gamma t3) with
          | Imp (a1, a2), Imp (b1, b2) ->
              if a1 = x1 && x2 = b1 && a2 = b2 then a2
              else (
                raise Type_error)
          | _ -> raise Type_error)
      | _ -> raise Type_error)
  | Absurd (_, ty) -> ty
  | Suc t -> if infer_type gamma t = Nat then Nat else raise Type_error
  | Zero -> Nat
  | Rec (n, z, s) -> (
      let type_z = infer_type gamma z in
      check_type gamma n Nat;
      match infer_type gamma s with
      | Imp (Nat, Imp (type_t, type_x)) when type_x = type_t && type_t = type_z
        ->
          type_z
      | _ -> raise Type_error)

and check_type gamma expr typ =
  if not (infer_type gamma expr = typ) then raise Type_error
;;


if Array.length Sys.argv > 1 && Sys.argv.(1) = "basic_proofs" then
  begin
check_type [] (Abs ("x", TVar "A", Var "x")) (Imp (TVar "A", TVar "A"));
try
  check_type [] (Abs ("x", TVar "A", Var "x")) (Imp (TVar "B", TVar "B"));
with Type_error -> (
  ();
  try
    check_type [] (Var "x") (TVar "A");
  with Type_error ->
    ();

    let and_comm =
      Abs ("x", And (TVar "A", TVar "B"), Pair (Snd (Var "x"), Fst (Var "x")))
    in
    print_endline "Preuve de la commutativité de /\\";
    print_endline (string_of_tm and_comm);
    print_endline (string_of_ty (infer_type [] and_comm));

    let truth = Abs ("x", Imp (True, TVar "A"), App (Var "x", Unit)) in
    print_endline "Preuve de (T => A) => A";
    print_endline (string_of_tm truth);
    print_endline (string_of_ty (infer_type [] truth));

    let disjunction =
      Abs
        ( "x",
          Or (TVar "A", TVar "B"),
          Case
            ( Var "x",
              Abs ("x", TVar "A", Right (TVar "B", Var "x")),
              Abs ("x", TVar "B", Left (Var "x", TVar "A")) ) )
    in
    print_endline "Preuve de la commutativité de \\/";
    print_endline (string_of_tm disjunction);
    print_endline (string_of_ty (infer_type [] disjunction));

    let falsity =
      Abs
        ( "x",
          And (TVar "A", Imp (TVar "A", Imp (TVar "B", False))),
          App (Snd (Var "x"), Fst (Var "x")) )
    in
    print_endline "Preuve de Faux => B";
    print_endline (string_of_tm falsity);
    print_endline (string_of_ty (infer_type [] falsity)))
  end
(* The lexer *)

let () = Printexc.record_backtrace true
exception Parse_error
let must_kwd s k = match Stream.next s with Genlex.Kwd k' when k' = k -> () | _ -> raise Parse_error
let peek_kwd s k = match Stream.peek s with Some (Genlex.Kwd k') when k' = k -> let _ = Stream.next s in true | _ -> false
let stream_is_empty s = try Stream.empty s; true with Stream.Failure -> false
let ident s = match Stream.next s with Genlex.Ident x -> x | _ -> raise Parse_error
let lexer = Genlex.make_lexer ["("; ")"; "=>"; "/\\"; "\\/"; "fun"; "->"; ","; ":"; "fst"; "snd"; "T"; "left"; "right"; "not"; "case"; "of"; "|"; "absurd"; "_"]
let ty_of_tk s =
  let rec ty () = arr ()
  and arr () =
    let a = prod () in
    if peek_kwd s "=>" then Imp (a, arr ()) else a
  and prod () =
    let a = sum () in
    if peek_kwd s "/\\" then And (a, prod ()) else a
  and sum () =
    let a = base () in
    if peek_kwd s "\\/" then Or (a, sum ()) else a
  and base () =
    match Stream.next s with
    | Genlex.Ident x -> TVar x
    | Genlex.Kwd "(" ->
       let a = ty () in
       must_kwd s ")";
       a
    | Genlex.Kwd "T" -> True
    | Genlex.Kwd "_" -> False
    | Genlex.Kwd "not" ->
       let a = base () in
       Imp (a, False)
    | _ -> raise Parse_error
  in
  ty ()
let tm_of_tk s =
  let noapp = List.map (fun k -> Some (Genlex.Kwd k)) [")"; ","; "case"; "fun"; "of"; "->"; "|"] in
  let ty () = ty_of_tk s in
  let rec tm () = app ()
  and app () =
    let t = ref (abs ()) in
    while not (stream_is_empty s) && not (List.mem (Stream.peek s) noapp) do
      t := App (!t, abs ())
    done;
    !t
  and abs () =
    if peek_kwd s "fun" then
      (
        must_kwd s "(";
        let x = ident s in
        must_kwd s ":";
        let a = ty () in
        must_kwd s ")";
        must_kwd s "->";
        let t = tm () in
        Abs (x, a, t)
      )
    else if peek_kwd s "case" then
      (
        let t = tm () in
        must_kwd s "of";
        let x = ident s in
        must_kwd s "->";
        let u = tm () in
        must_kwd s "|";
        let y = ident s in
        must_kwd s "->";
        let v = tm () in
        match t with 
        | Left (expr, typ) -> Case (t, Abs(x, (infer_type [] expr), u), Abs(y, typ, v))
        | Right (typ, expr) -> Case (t, Abs(x, typ, u), Abs(y, (infer_type [] expr), v))
        | _ -> raise Type_error 
      )
    else
      base ()
  and base () =
    match Stream.next s with
    | Genlex.Ident x -> Var x
    | Genlex.Kwd "(" ->
       if peek_kwd s ")" then
         Unit
       else
         let t = tm () in
         if peek_kwd s "," then
           let u = tm () in
           must_kwd s ")";
           Pair (t, u)
         else
           (
             must_kwd s ")";
             t
           )
    | Genlex.Kwd "fst" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ")";
       Fst t
    | Genlex.Kwd "snd" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ")";
       Snd t
    | Genlex.Kwd "left" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ",";
       let b = ty () in
       must_kwd s ")";
       Left (t, b)
    | Genlex.Kwd "right" ->
       must_kwd s "(";
       let a = ty () in
       must_kwd s ",";
       let t = tm () in
       must_kwd s ")";
       Right (a, t)
    | Genlex.Kwd "absurd" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ",";
       let a = ty () in
       must_kwd s ")";
       Absurd (t, a)
    | Kwd "Nat" -> Zero
    | _ -> raise Parse_error
  in
  tm ()
let ty_of_string a = ty_of_tk (lexer (Stream.of_string a))
let tm_of_string t = tm_of_tk (lexer (Stream.of_string t))



let rec string_of_ctx = function
  | [] -> ""
  | (a, b) :: [] -> a ^ " : " ^ string_of_ty b
  | (a, b) :: q -> a ^ " : " ^ string_of_ty b ^ " , " ^ string_of_ctx q

type sequent = context * ty

let proof = ref ""

let rm_last str =
  let nmax = ref (String.length str - 1) in
  while str.[!nmax] != '\n' do
    decr nmax
  done;
  String.sub str 0 !nmax

let string_of_seq = function a, b -> string_of_ctx a ^ " |- " ^ string_of_ty b

let rec prove env a =
  print_endline (string_of_seq (env, a));
  print_string "? ";
  flush_all ();
  let error e =
    print_endline e;
    proof := rm_last !proof;
    prove env a
  in
  let cmd, arg =
    let cmd = input_line stdin in
    proof := !proof ^ "\n" ^ cmd;
    let n = try String.index cmd ' ' with Not_found -> String.length cmd in
    let c = String.sub cmd 0 n in
    let a = String.sub cmd n (String.length cmd - n) in
    let a = String.trim a in
    (c, a)
  in
  match cmd with
  | "intro" -> (
      match a with
      | Imp (a, b) ->
          if arg = "" then error "Please provide an argument for intro."
          else
            let x = arg in
            let t = prove ((x, a) :: env) b in
            Abs (x, a, t)
      | And (a, b) ->
          let pa = prove env a and pb = prove env b in
          Pair (pa, pb)
      | True -> Unit
      | _ -> error "Don't know how to introduce this.")
  | "exact" -> (
      if arg = "" then error "Please provide an argument for exact."
      else
        try
          let t = tm_of_string arg in
          if infer_type env t <> a then error "Not the right type." else t
        with
        | Type_error -> error "Not a valid variable name."
        | e -> raise e)
  | "elim" -> (
      if arg = "" then error "Please provide an argument for elim."
      else
        let t = Var arg in
        try
          let f = infer_type env t in
          match f with
          | Imp (x, fx) when fx = a -> App (t, prove env x)
          | Imp (_, _) -> error "not valid type"
          | Or (x, y) ->
              let pa = prove ((arg, x) :: env) a
              and pb = prove ((arg, y) :: env) a in
              Case (t, Abs (arg, x, pa), Abs (arg, y, pb))
          | False -> Absurd (Var "", a)
          | Nat ->
              print_string ("Case " ^ arg ^ " = 0\n");
              let pa = prove env a in
              print_string ("Case " ^ arg ^ " = Suc " ^ arg ^ "\n");
              let pb = prove env (Imp (a, a)) in
              Rec (Var arg, pa, Abs (arg, Nat, pb))
          | _ -> error (arg ^ " is not a function")
        with
        | Type_error -> error "Variable not found"
        | e -> raise e)
  | "cut" ->
      if arg = "" then error "Please provide an argument for cut."
      else
        let x = ty_of_string arg in
        let f = prove env (Imp (x, a)) and b = prove env x in
        App (f, b)
  | "fst" -> (
      if arg = "" then error "Please provide an argument for elim."
      else
        let t = Var arg in
        try
          let f = infer_type env t in
          match f with
          | And (x, _) when x = a -> Fst t
          | And (_, _) -> error "not valid type"
          | _ -> error (arg ^ " is not a conjonction")
        with
        | Type_error -> error "Variable not found"
        | e -> raise e)
  | "snd" -> (
      if arg = "" then error "Please provide an argument for elim."
      else
        let t = Var arg in
        try
          let f = infer_type env t in
          match f with
          | And (_, x) when x = a -> Snd t
          | And (_, _) -> error "not valid type"
          | _ -> error (arg ^ " is not a conjonction")
        with
        | Type_error -> error "Variable not found"
        | e -> raise e)
  | "left" -> (
      match a with
      | Or (a, b) -> Left (prove env a, b)
      | _ -> error "It is not a disjunction")
  | "right" -> (
      match a with
      | Or (a, b) -> Right (a, prove env b)
      | _ -> error "It is not a disjunction")
  | "succ" -> (
      match a with
      | Nat -> Suc (prove env Nat)
      | _ -> error "Can't get successor of non-int")
  | "zero" -> (
      match a with
      | Nat -> Zero
      | _ -> error ("Zero is not of type " ^ string_of_ty a))
  | cmd -> error ("Unknown command: " ^ cmd)

let () =
  print_endline "Please enter the formula to prove:";
  let input = input_line stdin in
  let a = ty_of_string input in
  print_endline "Let's prove it.";
  proof := !proof ^ input;
  let t = prove [] a in
  print_endline "done.";
  print_endline "Proof term is";
  print_endline (string_of_tm t);
  print_string "Typechecking... ";
  flush_all ();
  assert (infer_type [] t = a);
  print_endline "ok.";
  print_endline "Do you want to save the list of commands used in a file? [y/N]";
  try
    let save = input_line stdin in
    if
      Array.exists
        (function x -> x = save)
        [| "y"; "Y"; "yes"; "Yes"; "o"; "O"; "oui"; "Oui" |]
    then (
      print_endline "Name of the file to save the proof [Default: out.proof]:";
      let file_in = input_line stdin in
      let file_name = if file_in = "" then "out.proof" else file_in in
      let file = open_out file_name in
      output_string file !proof)
  with End_of_file -> ()
