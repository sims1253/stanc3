(** The gathered-families registry table (W-108 increment 2 + W-115).

    One row per landed gathered-GLM stan-math primitive the compiler knows
    how to emit. The MIR matchers/rewrites themselves live in
    [Analysis_and_optimization.Optimize]; this module is the shared
    name/include table so the C++ backend can emit the right includes and
    per-observation push loops without depending on the optimizer. *)

(** How the primitive's result reaches [lp_accum__]:
    - [SingleVar] returns one var holding the whole log density (the
      expression-class families);
    - [PerObservation] returns one var per observation, which the generated
      model must push into the accumulator one by one to keep stock's
      chunked accumulation schedule bit-identical (the loop-class family,
      W-112 §2);
    - [TpLoop] is not a likelihood at all: it is the transformed-parameters
      LOOP rewrite (W-131) — the matched [for] loop over the predictor
      becomes a whole-vector assignment of the factory call's result, and
      the backend emits that assignment as a plain [y_hat = call;] (the
      gated hand-edit's exact shape) instead of [stan::model::assign]. *)
type emission = SingleVar | PerObservation | TpLoop

type t = {
  primitive : string  (** [StanLib] name of the emitted call *)
  ; header : string  (** [#include] the generated model needs when it fires *)
  ; emission : emission
  ; doc : string  (** one-line description of the matched Stan shape *)
}

(** The registry, in emission order. *)
val families : t list

(** The [StanLib] names of every registered primitive. *)
val primitives : string list

(** [emission_of name] is how [name]'s result is accumulated, if [name] is a
    registered primitive. *)
val emission_of : string -> emission option
