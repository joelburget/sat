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

  let pps = Fmt.(list pp ~sep:(any ", "))
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
  let get_literal = function [ lit ] -> Some lit | _ -> None

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
  let of_units literals = List.map literals ~f:List.return

  (** Remove every clause containing [lit], discard the complement from every clause
      containing it *)
  let propagate_unit clauses lit =
    List.fold clauses ~init:([], []) ~f:(fun (new_pure_lits, clauses) clause ->
        match true with
        | _ when Clause.contains_literal clause lit ->
          (* this clause is satisfied, drop it *)
          new_pure_lits, clauses
        | _ when Clause.contains_literal clause (Literal.complement lit) ->
          (* remove the unsatisfiable literal from this clause *)
          (match Clause.remove_unit (fst lit) clause with
          | [ lit ] -> lit :: new_pure_lits, clauses
          | clause -> new_pure_lits, clause :: clauses)
        | _ -> new_pure_lits, clause :: clauses)
  ;;

  let%expect_test "propagate_unit" =
    let clauses =
      [ []; [ 1, Polarity.Positive; 2, Negative ]; [ 1, Negative; 2, Positive ] ]
    in
    Fmt.pr "%a\n" pp clauses;
    let go clauses lit =
      let pp' ppf (new_pure_lits, clauses) =
        Fmt.pf
          ppf
          "{ new_pure_lits = [%a]; clauses = %a }"
          Fmt.(list Literal.pp ~sep:(any "; "))
          new_pure_lits
          pp
          clauses
      in
      Fmt.pr "propagate %a -> %a\n" Literal.pp lit pp' (propagate_unit clauses lit)
    in
    go clauses (1, Positive);
    go clauses (1, Negative);
    go clauses (2, Positive);
    go clauses (2, Negative);
    let clauses = [ [ 1, Polarity.Positive; 2, Negative ] ] in
    Fmt.pr "%a\n" pp clauses;
    go clauses (3, Negative);
    [%expect
      {|
      () ∧ (1 ∨ ¬2) ∧ (¬1 ∨ 2)
      propagate 1 -> { new_pure_lits = [2]; clauses = () }
      propagate ¬1 -> { new_pure_lits = [¬2]; clauses = () }
      propagate 2 -> { new_pure_lits = [1]; clauses = () }
      propagate ¬2 -> { new_pure_lits = [¬1]; clauses = () }
      (1 ∨ ¬2)
      propagate ¬3 -> { new_pure_lits = []; clauses = (1 ∨ ¬2) } |}]
  ;;

  (** Find variables that occur with only one polarity. *)
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
    Hashtbl.to_alist polarity_table
  ;;

  let%expect_test "pure_literals" =
    let go clauses =
      Fmt.(pr "pure literals %a -> %a\n" pp clauses Literal.pps (pure_literals clauses))
    in
    go [ []; [ 1, Positive; 2, Negative ]; [ 1, Negative; 2, Positive ] ];
    go [ []; [ 1, Positive; 2, Negative ]; [ 2, Positive ] ];
    go [ []; [ 1, Positive; 2, Positive ]; [ 2, Positive ] ];
    [%expect
      {|
      pure literals () ∧ (1 ∨ ¬2) ∧ (¬1 ∨ 2) ->
      pure literals () ∧ (1 ∨ ¬2) ∧ (2) -> 1
      pure literals () ∧ (1 ∨ 2) ∧ (2) -> 2, 1 |}]
  ;;

  module Literal_set = struct
    type t =
      | Inconsistent
      | Consistent of (int, Polarity.t) Hashtbl.t
      | Non_literal

    let pp ppf = function
      | Inconsistent -> Fmt.pf ppf "inconsistent"
      | Consistent table -> Fmt.pf ppf "{%a}" Literal.pps (Hashtbl.to_alist table)
      | Non_literal -> Fmt.pf ppf "non-literal"
    ;;
  end

  let get_consistent_literal_set clauses =
    match clauses |> List.map ~f:Clause.get_literal |> Option.all with
    | None -> Literal_set.Non_literal
    | Some literals ->
      let polarities = Hashtbl.create (module Int) in
      let is_consistent =
        List.fold literals ~init:true ~f:(fun consistent (v, polarity) ->
            if consistent
            then (
              match Hashtbl.find polarities v with
              | None ->
                Hashtbl.set polarities ~key:v ~data:polarity;
                true
              | Some polarity' -> Polarity.(polarity' = polarity))
            else false)
      in
      if is_consistent then Consistent polarities else Inconsistent
  ;;

  let%expect_test "get_consistent_literal_set" =
    let go clauses =
      Fmt.pr
        "get_consistent_literal_set %a -> %a\n"
        pp
        clauses
        Literal_set.pp
        (get_consistent_literal_set clauses)
    in
    go [ [] ];
    go [ [ 1, Positive; 2, Negative ]; [ 2, Positive ] ];
    go [ [ 1, Positive; 2, Positive ]; [ 2, Positive ] ];
    go [ [ 2, Negative ]; [ 2, Positive ] ];
    go [ [ 2, Positive ]; [ 2, Positive ] ];
    [%expect
      {|
      get_consistent_literal_set () -> non-literal
      get_consistent_literal_set (1 ∨ ¬2) ∧ (2) -> non-literal
      get_consistent_literal_set (1 ∨ 2) ∧ (2) -> non-literal
      get_consistent_literal_set (¬2) ∧ (2) -> inconsistent
      get_consistent_literal_set (2) ∧ (2) -> {2} |}]
  ;;
end

module Dpll = struct
  let unit_propagate clauses =
    let new_units, non_unit_clauses =
      List.partition_map clauses ~f:(function
          | [ lit ] -> Either.First lit
          | clause -> Second clause)
    in
    let non_unit_clauses = ref non_unit_clauses in
    let unit_clauses = Stack.of_list new_units in
    let new_units = ref new_units in
    Stack.until_empty unit_clauses (fun lit ->
        let new_pure_lits, new_clauses = Cnf.propagate_unit !non_unit_clauses lit in
        new_units := !new_units @ new_pure_lits;
        List.iter new_pure_lits ~f:(Stack.push unit_clauses);
        non_unit_clauses := new_clauses);
    !new_units, !non_unit_clauses
  ;;

  let pure_literal_elimination clauses =
    let pure_literals = Cnf.pure_literals clauses in
    let non_unit_clauses = ref clauses in
    let unit_clauses = Stack.create () in
    let new_units = ref pure_literals in
    let f lit =
      let new_pure_lits, new_clauses = Cnf.propagate_unit !non_unit_clauses lit in
      new_units := !new_units @ new_pure_lits;
      List.iter new_pure_lits ~f:(Stack.push unit_clauses);
      non_unit_clauses := new_clauses
    in
    List.iter pure_literals ~f;
    Stack.until_empty unit_clauses f;
    !new_units, !non_unit_clauses
  ;;

  exception Early_exit

  let check_clause_solubility clauses =
    if List.exists clauses ~f:Clause.is_empty then raise Early_exit
  ;;

  let dpll num_vars clauses =
    let rec go unsolved_vars clauses =
      match Cnf.get_consistent_literal_set clauses with
      | Inconsistent -> None
      | Consistent assignments ->
        unsolved_vars
        |> Set.to_list
        |> List.iter ~f:(fun key -> Hashtbl.set assignments ~key ~data:Polarity.Positive);
        Some assignments
      | Non_literal ->
        (try
           check_clause_solubility clauses;
           (* First perform unit propagation *)
           let unit_new_assignments, clauses = unit_propagate clauses in
           let clauses = Cnf.of_units unit_new_assignments @ clauses in
           check_clause_solubility clauses;
           (* Next perform pure literal elimination *)
           let pure_lit_new_assignments, clauses = pure_literal_elimination clauses in
           let clauses = Cnf.of_units pure_lit_new_assignments @ clauses in
           check_clause_solubility clauses;
           (* Finally, continue with remaining unsolved vars *)
           let newly_solved =
             List.map (unit_new_assignments @ pure_lit_new_assignments) ~f:fst
           in
           let unsolved_vars =
             Set.diff unsolved_vars (Set.of_list (module Int) newly_solved)
           in
           match Set.min_elt unsolved_vars with
           | Some chosen_var ->
             let unsolved_vars = Set.remove unsolved_vars chosen_var in
             (match go unsolved_vars ([ chosen_var, Positive ] :: clauses) with
             | None -> go unsolved_vars ([ chosen_var, Negative ] :: clauses)
             | result -> result)
           | None -> go unsolved_vars clauses
         with
        | Early_exit -> None)
    in
    let unsolved_vars = List.init num_vars ~f:Fn.id |> Set.of_list (module Int) in
    go unsolved_vars clauses
  ;;

  let%expect_test "dpll" =
    let pp_result ppf = function
      | None -> Fmt.pf ppf "none"
      | Some table -> Fmt.pf ppf "{%a}" Literal.pps (Hashtbl.to_alist table)
    in
    let go n clauses =
      Fmt.(pr "dpll %a -> %a\n" Cnf.pp clauses pp_result (dpll n clauses))
    in
    go 2 [ [ 0, Positive; 1, Negative ]; [ 0, Negative; 1, Positive ] ];
    go 2 [ [ 0, Positive; 1, Negative ]; [ 0, Positive; 1, Positive ] ];
    go 1 [ [ 0, Positive ]; [ 0, Negative ] ];
    go
      5
      [ [ 0, Positive; 1, Positive; 2, Positive ]
      ; [ 1, Positive; 2, Negative; 4, Negative ]
      ; [ 1, Negative; 5, Positive ]
      ];
    go
      3
      [ [ 0, Positive; 1, Positive ]
      ; [ 0, Positive; 1, Negative ]
      ; [ 0, Negative; 2, Positive ]
      ; [ 0, Negative; 2, Negative ]
      ];
    go
      8
      [ [ 0, Positive; 2, Positive ]
      ; [ 0, Positive; 1, Negative; 4, Negative ]
      ; [ 0, Positive; 4, Positive; 7, Positive ]
      ; [ 3, Negative; 1, Negative; 5, Positive ]
      ; [ 3, Negative; 4, Positive; 5, Negative ]
      ; [ 3, Positive; 4, Positive; 6, Negative ]
      ; [ 3, Positive; 6, Positive; 7, Negative ]
      ];
    [%expect
      {|
      dpll (0 ∨ ¬1) ∧ (¬0 ∨ 1) -> {1, 0}
      dpll (0 ∨ ¬1) ∧ (0 ∨ 1) -> {1, 0}
      dpll (0) ∧ (¬0) -> none
      dpll (0 ∨ 1 ∨ 2) ∧ (1 ∨ ¬2 ∨ ¬4) ∧ (¬1 ∨ 5) -> {1, 3, 2, ¬4, 5, 0}
      dpll (0 ∨ 1) ∧ (0 ∨ ¬1) ∧ (¬0 ∨ 2) ∧ (¬0 ∨ ¬2) -> none
      dpll (0 ∨ 2) ∧ (0 ∨ ¬1 ∨ ¬4) ∧ (0 ∨ 4 ∨ 7) ∧ (¬3 ∨ ¬1 ∨ 5) ∧ (¬3 ∨ 4 ∨ ¬5) ∧ (3 ∨ 4 ∨ ¬6) ∧ (3 ∨ 6 ∨ ¬7) -> {¬1, 3, 2, 7, 6, 4, ¬5, 0} |}]
  ;;
end
