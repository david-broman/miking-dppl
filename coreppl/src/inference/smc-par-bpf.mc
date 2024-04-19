include "../coreppl.mc"
include "../dppl-arg.mc"

lang ParallelBPFMethod = MExprPPL
  syn InferMethod =
  | ParallelBPF {particles : Expr}

  sem pprintInferMethod indent env =
  | ParallelBPF {particles = particles} ->
    let i = pprintIncr indent in
    match pprintCode i env particles with (env, particles) in
    (env, join ["(ParallelBPF {particles = ", particles, "})"])

  sem inferMethodFromCon info bindings =
  | "ParallelBPF" ->
    let expectedFields = [
      ("particles", int_ default.particles)
    ] in
    match getFields info bindings expectedFields with [particles] in
    ParallelBPF {particles = particles}

  sem inferMethodFromOptions options =
  | "smc-par-bpf" ->
  ParallelBPF {particles = int_ options.particles}

  sem inferMethodConfig info =
  | ParallelBPF {particles = particles} ->
    fieldsToRecord info [("particles", particles)]

  sem typeCheckInferMethod env info =
  | ParallelBPF {particles = particles} ->
    let int = TyInt {info = info} in
    let particles = typeCheckExpr env particles in
    unify env [info, infoTm particles] int (tyTm particles);
    ParallelBPF {particles = particles}

  sem inferSmapAccumL_Expr_Expr f acc =
  | ParallelBPF r ->
    match f acc r.particles with (acc, particles) in
    (acc, ParallelBPF {r with particles = particles})

  sem setRuns expr =
  | ParallelBPF r -> ParallelBPF {r with particles = expr}

end
