(** Solvable polynomial maps.  A polynomial map [f : Q^n -> Q^n] is
   solvable if its circular dependencies are linear (e.g. [f(x,y) =
   (x+1,y+x^2)] is solvable but [f(x,y) = (y^2,x)] is not).  *)

open Syntax
open Iteration

(** Solvable polynomial maps with eigenvalue 1.  Closed forms are
   polynomial. *)
module SolvablePolynomialOne : PreDomainWedge

(** Solvable polynomial maps without spectral assumptions.  Closed
   forms may use operators from Berg's operational calculus,
   represented as uninterpreted function symbols that will be
   allocated upon calling [exp]. *)
module SolvablePolynomial : PreDomainWedge

(** Solvable polynomial maps with periodic rational eigenvalues.
   Closed forms are exponential polynomials. *)
module SolvablePolynomialPeriodicRational : PreDomainWedge

(** Extends [SolvablePolynomialPeriodicRational] with universally
   quantified precondition expressed over terms with
   Presurger-definable dynamics. *)
module PresburgerGuard : PreDomain

type 'a dlts_abstraction =
  { dlts : Linear.PartialLinearMap.t;
    simulation : ('a term) array }

(** Deterministic linear transition systems *)
module DLTS : PreDomain with type 'a t = 'a dlts_abstraction

module DLTSPeriodicRational : sig
  include PreDomain with type 'a t = 'a dlts_abstraction

  (** Find best abstraction as a DLTS with rational (rather than
     periodic rational) spectrum *)
  val abstract_rational : ?exists:(symbol -> bool) ->
    'a context ->
    (symbol * symbol) list ->
    'a formula ->
    'a t
end

(** External entry-point used by CHORA *)
val exp_ocrs_external :
   'a Syntax.context ->
   (Syntax.Symbol.Map.key * Syntax.symbol) list ->
   'a Syntax.term ->
   'a Syntax.term array ->
   int -> 
   QQ.t array array list -> 
   Polynomial.QQXs.t array list -> 
   'a Syntax.formula
