include "../dists.mc"
include "../../inference/smc.mc"
include "../../cfa.mc"

include "mexpr/ast-builder.mc"
include "mexpr/cps.mc"

lang MExprPPLParallelBPF =
  MExprPPL + Resample + TransformDist + MExprCPS + MExprANFAll + MExprPPLCFA

  -------------------------
  -- Boostrapped particle filter (SMC) with parallelization
  -------------------------

  sem transformProb =
  | TmAssume t ->
    let i = withInfo t.info in
    i (app_ (i (var_ "sample")) t.dist)

  | TmObserve t ->
    let i = withInfo t.info in
    let weight = i (appf2_ (i (var_ "logObserve")) t.dist t.value) in
    i (appf2_ (i (var_ "updateWeight")) weight (i (var_ "state")))
  | TmWeight t ->
    let i = withInfo t.info in
    i (appf2_ (i (var_ "updateWeight")) t.weight (i (var_ "state")))
  | TmResample t -> withInfo t.info unit_
  | t -> t


  -------------------------------
  -- IMPORTANCE SAMPLING (CPS) --
  -------------------------------

  -- CPS compile  
  sem exprCps env k =
  -- Do nothing at assumes or resamples
  | TmLet ({ body = TmAssume _ } & t) ->
    TmLet { t with inexpr = exprCps env k t.inexpr }
  | TmLet ({ body = TmResample _ } & t) ->
    TmLet { t with inexpr = exprCps env k t.inexpr }
  | TmLet ({ body = TmDist _ } & t) ->
    TmLet { t with inexpr = exprCps env k t.inexpr }

  -- This is where we use the continuation (weight and observe)
  | TmLet { ident = ident, body = TmWeight { weight = weight },
            inexpr = inexpr} & t ->
    let i = withInfo (infoTm t) in
    let k =
      if tailCall t then
        match k with Some k then k
        else error "Something went wrong with partial CPS transformation"
      else i (nulam_ ident (exprCps env k inexpr))
    in
    i (appf2_ (i (var_ "updateWeight")) weight k)

  -- This is where we use the continuation (weight and observe)
  | TmLet { ident = ident, body = TmObserve { value = value, dist = dist },
            inexpr = inexpr } & t ->
    let i = withInfo (infoTm t) in
    let k =
      if tailCall t then
        match k with Some k then k
        else error "Something went wrong with partial CPS transformation"
      else i (nulam_ ident (exprCps env k inexpr))
    in
    let weight = i (appf2_ (i (var_ "logObserve")) dist value) in
    i (appf2_ (i (var_ "updateWeight")) weight k)

  -- NOTE(2023-08-08,dlunde): Many TmTypes are shared with non-PPL code and
  -- transformed versions are removed when removing duplicate code.
  -- Therefore, we have to simply replace TyCon and TyApp with Unknown here.
  sem tyCps env =
  | (TyCon { info = info } | TyApp { info = info } ) ->
    let i = tyWithInfo info in i tyunknown_

  sem transformProbCps =
  | TmAssume t ->
    let i = withInfo t.info in
    i (app_ (i (var_ "sample")) t.dist)
  | TmResample t -> withInfo t.info unit_

  -- Should already have been removed by CPS!
  | (TmObserve _ | TmWeight _) & tm ->
    errorSingle [infoTm tm] "Impossible in importance sampling with CPS"
  | t -> t

  sem compileCps : Options -> (Expr,Expr) -> Expr
  sem compileCps options =
  | (_,t) ->

    -- printLn ""; printLn "--- INITIAL ANF PROGRAM ---";
    -- match pprintCode 0 pprintEnvEmpty t with (env,str) in
    -- printLn (str);

    let t =
      let cont = (ulam_ "x" (conapp_ "End" (var_ "x"))) in
      cpsFullCont cont t
    in  

    -- printLn ""; printLn "--- AFTER CPS ---";
    -- match pprintCode 0 pprintEnvEmpty t with (env,str) in
    -- printLn (str);

    -- Transform distributions to MExpr distributions
    let t = mapPre_Expr_Expr transformTmDist t in

    -- Transform samples, observes, and weights to MExpr
    let t = mapPre_Expr_Expr transformProbCps t in
    t
end

let compilerParallelBPF = lam options. use MExprPPLParallelBPF in
    ("smc-par-bpf/runtime-cps.mc", compileCps options)
