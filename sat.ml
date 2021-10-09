let () =
  let problem = Nominal_problem.And (Or (Var "a", Not (Var "b")), Not (Var "a")) in
  Fmt.pr "problem: %a\n" Nominal_problem.pp problem;
  let problem' = (Named_index_problem.of_nominal problem).problem in
  match Index_problem.brute_force 2 problem' with
  | Some assignment ->
    Fmt.pr
      "found assignment: %a (eval to %b)"
      Assignment.pp
      assignment
      (Index_problem.eval assignment problem')
  | None -> Fmt.pr "no assignment found"
;;
