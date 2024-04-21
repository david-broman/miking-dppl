
include "common.mc"

include "ext/dist-ext.mc"
include "ext/math-ext.mc"
include "seq.mc"
include "string.mc"
include "tensor.mc"

include "../runtime-common.mc"
include "../runtime-dists.mc"
 
-- In importance sampling, the state is simply the accumulated weight.
--type State = Ref Float
type State = (Tensor[Float], Int)

--let updateWeight = lam v. lam state. modref state (addf (deref state) v)
let updateWeight = lam v. lam state. 
  tensorSetExn state.0 [state.1] (addf (tensorGetExn state.0 [state.1]) v)

let unwrapOpt : all a. Option a -> a = lam o.
  match o with Some x then x
  else error "Could not unwrap option"

recursive 
  let sim_particles = lam i. lam a. lam acc. lam model.
    if eqi i 0 then acc 
    else 
      let r = model (a, (subi i 1)) in
      sim_particles (subi i 1) a (cons r acc) model
end

-- General inference algorithm for importance sampling
let run : all a. Unknown -> (State -> a) -> use RuntimeDistBase in Dist a = 
  lam config. lam model.
  use RuntimeDist in

  let particles = config.particles in

  let weightInit = 0.0 in
--  let states = createList particles (lam. ref weightInit) in
  let warray = tensorCreateDense [particles] (lam. weightInit) in
--  let res = mapReverse model states in
  let res = sim_particles particles warray [] model in
--  let weights = mapReverse deref states in
  let weights = tensorToSeqExn warray in
  constructDistEmpirical res weights
    (EmpNorm { normConst = normConstant weights })
