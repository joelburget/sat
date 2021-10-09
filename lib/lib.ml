open Base

module Nominal_problem = struct
  type t =
    | Var of string
    | And of t * t
    | Or of t * t
    | Not of t

  let pp =
    (* a \/ b -> a /\ b -> ~a, a
     * 0         1         2
     *)
    let open Fmt in
    let rec go prec ppf = function
      | Var name -> pf ppf "%s" name
      | Not a -> pf ppf "¬%a" (go 2) a
      | And (a, b) ->
        pf ppf (if prec > 1 then "(%a ∧ %a)" else "%a ∧ %a") (go 1) a (go 1) b
      | Or (a, b) ->
        pf ppf (if prec > 0 then "(%a ∨ %a)" else "%a ∨ %a") (go 0) a (go 0) b
    in
    go 0
  ;;

  let rec vars = function
    | Var x -> Set.singleton (module String) x
    | And (x, y) | Or (x, y) -> Set.union (vars x) (vars y)
    | Not x -> vars x
  ;;
end

module Assignment = struct
  type t = bool list

  let pp ppf = Fmt.(pf ppf "[%a]" (list bool ~sep:(any ", ")))
end

module Index_problem = struct
  type t =
    | Var of int
    | And of t * t
    | Or of t * t
    | Not of t

  let rec pp_machine ppf = function
    | Var i -> Fmt.int ppf i
    | And (x, y) -> Fmt.pf ppf "and(%a;%a)" pp_machine x pp_machine y
    | Or (x, y) -> Fmt.pf ppf "or(%a;%a)" pp_machine x pp_machine y
    | Not x -> Fmt.pf ppf "not(%a)" pp_machine x
  ;;

  let eval assignments problem =
    let rec go = function
      | Var i -> List.nth_exn assignments i
      | And (x, y) -> go x && go y
      | Or (x, y) -> go x || go y
      | Not x -> not (go x)
    in
    go problem
  ;;

  let brute_force n_vars problem =
    let rec go assignments n_vars =
      match n_vars with
      | 0 -> if eval assignments problem then Some assignments else None
      | _ ->
        Option.first_some
          (go (true :: assignments) (n_vars - 1))
          (go (false :: assignments) (n_vars - 1))
    in
    go [] n_vars
  ;;
end

module Named_index_problem = struct
  type t =
    { vars : string list
    ; problem : Index_problem.t
    }

  let to_nominal { vars; problem } =
    let rec go = function
      | Index_problem.Var i -> Nominal_problem.Var (List.nth_exn vars i)
      | And (x, y) -> And (go x, go y)
      | Or (x, y) -> Or (go x, go y)
      | Not x -> Not (go x)
    in
    go problem
  ;;

  let of_nominal problem =
    let vars = problem |> Nominal_problem.vars |> Set.to_list in
    let rec go = function
      | Nominal_problem.Var name ->
        (match List.findi vars ~f:(fun _ name' -> String.(name = name')) with
        | None -> Fmt.failwith "couldn't find var %s" name
        | Some (i, _) -> Index_problem.Var i)
      | And (x, y) -> And (go x, go y)
      | Or (x, y) -> Or (go x, go y)
      | Not x -> Not (go x)
    in
    { vars; problem = go problem }
  ;;

  let pp ppf problem = Nominal_problem.pp ppf (to_nominal problem)
end

module Polarity = struct
  type t =
    | Positive
    | Negative

  let ( = ) a b =
    match a, b with Positive, Positive -> true | Negative, Negative -> true | _ -> false
  ;;

  let negate = function Positive -> Negative | Negative -> Positive
end

module Literal = struct
  type t = int * Polarity.t

  let pp ppf (i, polarity) =
    match polarity with
    | Polarity.Positive -> Fmt.int ppf i
    | Negative -> Fmt.pf ppf "¬%d" i
  ;;

  let complement (i, polarity) = i, Polarity.negate polarity
  let ( = ) (i1, p1) (i2, p2) = Int.(i1 = i2) && Polarity.(p1 = p2)

  let%expect_test _ =
    let lit = 1, Polarity.Negative in
    Fmt.pr "%a -> %a\n" pp lit pp (complement lit);
    [%expect {|
    ¬1 -> 1
  |}]
  ;;
end

module Clause = struct
  (** A disjunction of literals. Note: representing an (unordered) set. *)
  type t = Literal.t list

  let pp ppf lits = Fmt.(pf ppf "(%a)" (list ~sep:(any " ∨ ") Literal.pp) lits)
  let is_empty = List.is_empty
  let remove_unit v = List.filter ~f:(fun (v', _) -> Int.(v <> v'))
  let contains_literal = List.mem ~equal:Literal.( = )

  let%expect_test _ =
    let clause = [] in
    Fmt.pr
      "%a %b %b %a\n"
      pp
      clause
      (is_empty clause)
      (contains_literal clause (1, Polarity.Positive))
      pp
      (remove_unit 1 clause);
    let clause = [ 1, Polarity.Positive; 2, Polarity.Negative ] in
    Fmt.pr
      "%a %b %b %b %a\n"
      pp
      clause
      (is_empty clause)
      (contains_literal clause (1, Polarity.Positive))
      (contains_literal clause (1, Polarity.Negative))
      pp
      (remove_unit 1 clause);
    [%expect {|
    () true false ()
    (1 ∨ ¬2) false true false (¬2)
  |}]
  ;;
end

module Cnf = struct
  (** A conjunction of disjunctions (clauses). Note: representing an (unordered) set. *)
  type t = Clause.t list

  let pp = Fmt.(list ~sep:(any " ∧ ") Clause.pp)

  (** Remove every clause containing [lit], discard the complement from every clause
      containing it *)
  let unit_propagate clauses lit =
    List.fold clauses ~init:[] ~f:(fun clauses clause ->
        if Clause.contains_literal clause lit
        then clauses
        else if Clause.contains_literal clause (Literal.complement lit)
        then Clause.remove_unit (fst lit) clause :: clauses
        else clauses)
  ;;

  let%expect_test "unit_propagate" =
    let clauses =
      [ []
      ; [ 1, Polarity.Positive; 2, Polarity.Negative ]
      ; [ 1, Polarity.Negative; 2, Polarity.Positive ]
      ]
    in
    Fmt.pr "%a\n" pp clauses;
    let go lit =
      Fmt.pr "propagate %a -> %a\n" Literal.pp lit pp (unit_propagate clauses lit)
    in
    go (1, Polarity.Positive);
    go (1, Polarity.Negative);
    go (2, Polarity.Positive);
    go (2, Polarity.Negative);
    [%expect
      {|
      () ∧ (1 ∨ ¬2) ∧ (¬1 ∨ 2)
      propagate 1 -> (2)
      propagate ¬1 -> (¬2)
      propagate 2 -> (1)
      propagate ¬2 -> (¬1) |}]
  ;;

  (** Remove [v] from every clause, discard clauses that are now empty *)
  let pure_literal_assign clauses v =
    List.fold clauses ~init:[] ~f:(fun clauses clause ->
        match Clause.remove_unit v clause with
        | [] -> clauses
        | clause -> clause :: clauses)
  ;;

  let%expect_test "pure_literal_assign" =
    let clauses =
      [ []
      ; [ 1, Polarity.Positive; 2, Polarity.Negative ]
      ; [ 1, Polarity.Negative; 2, Polarity.Positive ]
      ]
    in
    Fmt.pr "%a\n" pp clauses;
    Fmt.pr "assign 1 -> %a\n" pp (pure_literal_assign clauses 1);
    Fmt.pr "assign 2 -> %a\n" pp (pure_literal_assign clauses 2);
    [%expect
      {|
      () ∧ (1 ∨ ¬2) ∧ (¬1 ∨ 2)
      assign 1 -> (2) ∧ (¬2)
      assign 2 -> (¬1) ∧ (1) |}]
  ;;

  let pure_literals clauses =
    let polarity_table = Hashtbl.create (module Int) in
    let tombstones = Hash_set.create (module Int) in
    List.iter clauses ~f:(fun clause ->
        List.iter clause ~f:(fun (v, polarity) ->
            match Hashtbl.find polarity_table v with
            | None ->
              if not (Hash_set.mem tombstones v)
              then Hashtbl.add_exn polarity_table ~key:v ~data:polarity
            | Some polarity' ->
              if not Polarity.(polarity' = polarity)
              then (
                Hashtbl.remove polarity_table v;
                Hash_set.add tombstones v)));
    Hashtbl.keys polarity_table
  ;;

  let%expect_test "pure_literals" =
    let pp_list = Fmt.(list int ~sep:(any ", ")) in
    let go clauses =
      Fmt.(pr "pure literals %a -> %a\n" pp clauses pp_list (pure_literals clauses))
    in
    go
      [ []
      ; [ 1, Polarity.Positive; 2, Polarity.Negative ]
      ; [ 1, Polarity.Negative; 2, Polarity.Positive ]
      ];
    go [ []; [ 1, Polarity.Positive; 2, Polarity.Negative ]; [ 2, Polarity.Positive ] ];
    go [ []; [ 1, Polarity.Positive; 2, Polarity.Positive ]; [ 2, Polarity.Positive ] ];
    [%expect
      {|
      pure literals () ∧ (1 ∨ ¬2) ∧ (¬1 ∨ 2) ->
      pure literals () ∧ (1 ∨ ¬2) ∧ (2) -> 1
      pure literals () ∧ (1 ∨ 2) ∧ (2) -> 2, 1 |}]
  ;;
end

module Dpll = struct
  let dpll num_vars clauses =
    let rec go var_assignments clauses =
      (* Fmt.pr "go [%a] %a\n" Fmt.(list bool ~sep:(any ", ")) var_assignments Cnf.pp clauses; *)
      let var_num = List.length var_assignments in
      if Int.(var_num = num_vars)
      then
        (* Fmt.pr "go returning (1)\n"; *)
        Some var_assignments
        (* XXX have we checked the last assignment? *)
      else if clauses |> List.find ~f:Clause.is_empty |> Option.is_some
      then (* Fmt.pr "go returning (2)\n"; *)
        None
      else (
        (* Fmt.pr "else branch clauses: %a\n" Cnf.pp clauses; *)
        let clauses =
          List.fold clauses ~init:clauses ~f:(fun clauses clause ->
              match clause with [ lit ] -> Cnf.unit_propagate clauses lit | _ -> clauses)
        in
        (* Fmt.pr "clauses after unit propagation: %a\n" Cnf.pp clauses; *)
        let clauses =
          List.fold (Cnf.pure_literals clauses) ~init:clauses ~f:Cnf.pure_literal_assign
        in
        (* Fmt.pr "clauses after pure literal assignment: %a\n" Cnf.pp clauses; *)
        if List.for_all clauses ~f:Clause.is_empty
        then None
        else (
          match go (true :: var_assignments) ([ var_num, Positive ] :: clauses) with
          | None -> go (false :: var_assignments) ([ var_num, Negative ] :: clauses)
          | result -> result))
    in
    go [] clauses
  ;;

  let%expect_test "dpll" =
    let go n clauses =
      Fmt.(
        pr
          "dpll %a -> %a\n"
          Cnf.pp
          clauses
          (option ~none:(any "none") (brackets (list bool ~sep:(any ", "))))
          (dpll n clauses))
    in
    go
      2
      [ [ 1, Polarity.Positive; 2, Polarity.Negative ]
      ; [ 1, Polarity.Negative; 2, Polarity.Positive ]
      ];
    go
      2
      [ [ 1, Polarity.Positive; 2, Polarity.Negative ]
      ; [ 1, Polarity.Positive; 2, Polarity.Positive ]
      ];
    go 1 [ [ 0, Polarity.Positive ]; [ 0, Polarity.Negative ] ];
    [%expect
      {|
      dpll (1 ∨ ¬2) ∧ (¬1 ∨ 2) -> [true, true]
      dpll (1 ∨ ¬2) ∧ (1 ∨ 2) -> [true, true]
      dpll (1) ∧ (¬1) -> none |}]
  ;;
end
