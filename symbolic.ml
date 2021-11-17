open Tagless_impl
open Tagless_fft
open Tagless_types

module NewHope_param = struct
  let q = 12289

  let qinv = 12287

  let omega = 49

  let n = 1024

end

module D_symbolic = struct
  include Tagless_impl.R

  type exp =
    | Const of int
    | Sym of string
    | Add of exp * exp
    | Sub of exp * exp
    | Mul of exp * exp

  type t = exp

  let lift e = fun () -> e

  let one = Const 1

  let q = NewHope_param.q

  let add' x y =
    match x, y with
    | Const(c1), Const(c2) -> Const ((c1 + c2) mod q)
    | Const(c1), _ when c1 = 0 -> y
    | _, Const(c2)  when c2 = 0 -> x
    | _ -> Add(x, y)

  let add x y =
    let x = x () in
    let y = y () in
    lift (add' x y)

  let sub' x y =
    match x, y with
    | Const(c1), Const(c2) -> Const ((c1 - c2) mod q)
    | _, Const(c2)  when c2 = 0 -> x
    | _ -> Sub(x, y)

  let sub x y =
    let x = x () in
    let y = y () in
    lift (sub' x y)

  let mul' x y =
    match x, y with
    | Const(c1), Const(c2) -> Const ((c1 * c2) mod q)
    | Const(c1), _ when c1 = 1 -> y
    | _, Const(c2)  when c2 = 1 -> x
    | Mul(lhs, Const(c1)), Const(c2) -> Mul(lhs, Const((c1 * c2) mod q))
    | _ -> Mul(x, y)

  let mul x y =
    let x = x () in
    let y = y () in
    lift (mul' x y)

  type _ c_type +=
    | CExp: exp c_type

  let domain_c_type = CExp

  let barret_reduce x = x

  let primitive_root_power _ j =
    let open Tagless_fft in
    let module Prim_roots = Primitive_roots_int(NewHope_param)(struct let factor = 1 end) in
    let w = Prim_roots.primitive_root_power NewHope_param.n j in
    Const w

  let rec poly_simplify = function
    | Mul(x, y) -> begin match x with
        | Add(x2, y2) ->
          add' (poly_simplify (mul' (poly_simplify x2) y))
            (poly_simplify (mul' (poly_simplify y2) y))
        | Sub(x2, y2) ->
          sub' (poly_simplify (mul' (poly_simplify x2) y))
            (poly_simplify (mul' (poly_simplify y2) y))
        | Mul(x2, y2) ->
          mul' (mul' (poly_simplify x2) (poly_simplify y2)) y
        | _ -> Mul(x, y)
      end
    | Add(x, y) -> add' (poly_simplify x) (poly_simplify y)
    | Sub(x, y) -> sub' (poly_simplify x) (poly_simplify y)
    | x -> x

end

open D_symbolic

let rec string_of_exp = function
  | Const(c) -> string_of_int c
  | Sym(name) -> name
  | Add(x, y) ->
    Printf.sprintf "%s + %s" (string_of_exp x) (string_of_exp y)
  | Sub(x, y) ->
    let x_str = (string_of_exp x) in
    let y_str = (string_of_exp y) in
    begin match y with
      | Add(_) | Sub(_) ->  Printf.sprintf "%s - (%s)" x_str y_str
      | _ ->     Printf.sprintf "%s - %s" x_str y_str
    end
  | Mul(x, y) ->
    let x_str = (string_of_exp x) in
    let y_str = (string_of_exp y) in
    let lhs =
      match x with
      | Add _ | Sub _ -> Printf.sprintf "(%s)" x_str
      | _ -> Printf.sprintf "%s" x_str
    in
    let rhs =
      match y with
      | Add _ | Sub _ -> Printf.sprintf "(%s)" y_str
      | _ -> Printf.sprintf "%s" y_str
    in
    Printf.sprintf "%s * %s" lhs rhs

let get_poly_coeff p =
  let p = poly_simplify p in
  let coeff = Array.init NewHope_param.n (fun _ -> 0) in
  let sign = Array.init NewHope_param.n (fun _ -> 0) in
  let var_name_to_int name =
    let id = String.sub name 1 ((String.length name) - 1) in
    int_of_string id in
  let rec visit term is_negative = match term with
    | Mul(Sym(var_name), Const(v)) ->
      let id = var_name_to_int var_name in
      coeff.(id) <- v;
      sign.(id) <- if is_negative then -1 else 1
    | Add(x, y) ->
      visit x is_negative;
      visit y is_negative
    | Sub(x, y) ->
      visit x is_negative;
      visit y (not is_negative)
    | Sym(var_name) ->
      let id = var_name_to_int var_name in
      coeff.(id) <- 1;
      sign.(id) <- if is_negative then -1 else 1
    | _ -> assert false
  in
  visit p false;
  Array.init NewHope_param.n (fun i -> coeff.(i) * sign.(i))


(* let test_simplify =
 *   let open D_symbolic in
 *   let p = mul' (mul' (add' (Sym "x0") (Sym "x1")) (Const 5)) (Const 6) in
 *   Printf.printf "%s\n" (string_of_exp (poly_simplify p)) *)

let test_poly_coefficients =
  let size = 1024 in
  let module R_NTT = FFT_lazy_gen(R_Array)(D_symbolic) in
  let open R_Array in
  let arr = (arr_init size (fun i ->
      let vname = Printf.sprintf "x%d" i in
      (fun () -> Sym vname))) () in
  let fn = (R_NTT.fft size) () in
  fn arr;
  Array.init size (fun idx ->
      let p = arr.(idx) in
      (* Printf.printf "%s\n" (string_of_exp (D_symbolic.poly_simplify p)); *)
      let coeffs_fft = get_poly_coeff p in
      let module Prim_roots = Fft_domain.Primitive_roots(Fft_types.IntegerModulo(NewHope_param)) in
      let n = NewHope_param.n in
      let coeffs_dft = Prim_roots.powers n n idx in
      Array.init size (fun i ->
          let coeff_fft = coeffs_fft.(i) in
          let coeff_dft = coeffs_dft.(i) in
          let coeff_fft =
            if coeff_fft < 0 then begin
              (* Printf.printf "negative coeff %d\n" coeff_fft; *)
              coeff_fft + NewHope_param.q
            end
            else coeff_fft in
          assert (coeff_dft = coeff_fft)))
          (* Printf.printf "%d: %d, %d\n" i coeff_fft coeff_dft); *)
