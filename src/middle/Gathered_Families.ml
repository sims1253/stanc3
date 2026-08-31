(** The gathered-families registry table (W-108 increment 2 + W-115).

    One row per landed gathered-GLM stan-math primitive the compiler knows
    how to emit. The MIR matchers/rewrites themselves live in
    [Analysis_and_optimization.Optimize] (each one recognizes the Stan shape
    named in [doc] in the reverse-mode log prob and replaces it with a call
    to [primitive]); this module is the shared name/include table so the
    C++ backend can emit the right includes and per-observation push loops
    without depending on the optimizer. Adding a family is one row here plus
    one matcher there — no other wiring. *)

open Std

type emission = SingleVar | PerObservation | TpLoop

type t = {
  primitive : string  (** [StanLib] name of the emitted call *)
  ; header : string  (** [#include] the generated model needs when it fires *)
  ; emission : emission
  ; doc : string  (** one-line description of the matched Stan shape *)
}

let families =
  [ { primitive= "bernoulli_logit_lpmf_gathered"
    ; header= "stan/math/rev/prob/bernoulli_logit_lpmf_gathered.hpp"
    ; emission= SingleVar
    ; doc=
        "2PL IRT likelihood y ~ bernoulli_logit(alpha[ii] .* (theta[jj] - \
         beta[ii])) (W-108)" }
  ; { primitive= "dot_self_gathered_diff"
    ; header= "stan/math/rev/fun/dot_self_gathered_diff.hpp"
    ; emission= SingleVar
    ; doc=
        "gathered ICAR prior -(0.5) * dot_self(phi[node1] - phi[node2]) \
         (W-113)" }
  ; { primitive= "normal_lpdf_gathered"
    ; header= "stan/math/rev/prob/normal_lpdf_gathered.hpp"
    ; emission= PerObservation
    ; doc=
        "loop-form normal likelihood for (n in 1:N) { mu[n] = alpha[ii[n]] \
         [+ x[n] * beta[ii2[n]]]; target += normal_lpdf(y[n] | mu[n], sigma) \
         } (W-112)" }
  ; { primitive= "gathered_additive_tp"
    ; header= "stan/math/rev/prob/bernoulli_logit_lpmf_gathered.hpp"
    ; emission= TpLoop
    ; doc=
        "tp-built gathered-additive predictor for (i in 1:N) { y_hat[i] = \
         beta[1] + beta[2]*xd[i] ... + a[idx[i]] } with y_hat's only other use \
         a downstream likelihood — the loop becomes the per-element custom-vari \
         factory call, the likelihood stays stock (W-131)" } ]

let primitives = List.map families ~f:(fun f -> f.primitive)

let emission_of name =
  match List.find_opt families ~f:(fun fam -> String.equal fam.primitive name) with
  | Some fam -> Some fam.emission
  | None -> None
