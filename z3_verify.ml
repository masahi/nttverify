module NewHope_param = struct
  let q = 12289
  let qinv = 12287
  let omega = 49
  let n = 1024
end

module type Base_Arith = sig
  type 'a expr
  type uint16

  val const : int -> uint16 expr   (* constant *)
  val (%+) : uint16 expr -> uint16 expr -> uint16 expr
  val (%-) : uint16 expr -> uint16 expr -> uint16 expr
  val (%&) : uint16 expr -> uint16 expr -> uint16 expr
  val (%>>) : uint16 expr -> uint16 expr -> uint16 expr
  val mulhi: uint16 expr -> uint16 expr -> uint16 expr
  val mullo: uint16 expr -> uint16 expr -> uint16 expr
  val not_zero: uint16 expr -> uint16 expr
end

module ModularArith(A: Base_Arith) = struct
  open A
  module Param = NewHope_param

  let rlog = 16
  let q = Param.q
  let r = (Int.shift_left 1 rlog)

  let csub x =
    let tmp_sub = x %- (const q) in
    let tmp_sra = tmp_sub %>> (const 15) in
    let tmp_and = tmp_sra %& (const q) in
    tmp_sub %+ tmp_and

  let barrett_reduce x =
    let mul_5 = mulhi x (const 5) in
    x %- (mullo mul_5 (const q))

  let montgomery_multiply_reduce x y =
    let mlo = mullo x y in
    let mhi = mulhi x y in
    let mlo_qinv = mullo mlo (const Param.qinv) in
    let t = mulhi mlo_qinv (const Param.q) in
    let carry = not_zero mlo in
    let res = mhi %+ t %+ carry in
    csub res
end

open Z3
open Z3.BitVector

module Z3_Arith = struct
  type 'a expr = Z3.Expr.expr
  type uint16 = int

  let ctx = mk_context []
  let bits = 16

  let const n = mk_numeral ctx (string_of_int n) bits
  let (%+) x y = mk_add ctx x y
  let (%-) x y = mk_sub ctx x y
  let (%&) x y = mk_and ctx x y
  let (%>>) x shift = mk_ashr ctx x shift
  let not_zero x = Boolean.mk_ite ctx (mk_ugt ctx x (const 0)) (const 1) (const 0)
  let mullo x y = mk_mul ctx x y
  let mulhi x y =
    let to_u32 v =
      mk_concat ctx (const 0) v in
    mk_extract ctx 31 16 (mk_mul ctx (to_u32 x) (to_u32 y))
end

module Mod = ModularArith(Z3_Arith)

open Z3_Arith
open Mod

let barrett_reduce_ref x =
  mk_urem ctx x (const NewHope_param.q)

let to_u32 v =
  mk_concat ctx (const 0) v

let const_32 c =
  mk_numeral ctx (string_of_int c) 32

let mul_red_ref x y =
  let mul = mk_mul ctx (to_u32 x) (to_u32 y) in
  let urem_32 = mk_urem ctx mul (const_32 NewHope_param.q) in
  mk_extract ctx 15 0 urem_32

let verify_eq ref_res opt_res =
  let solver = Z3.Solver.mk_solver ctx None in
  let _ = Z3.Solver.add solver [Boolean.mk_not ctx (Boolean.mk_eq ctx ref_res opt_res)] in
  match Z3.Solver.check solver [] with
    | UNSATISFIABLE -> ()
    | _ -> assert false

let test_barrett_reduce () =
  let x = mk_const_s ctx "x" bits in
  let ref_res = barrett_reduce_ref x in
  let opt_res = csub (barrett_reduce x) in
  verify_eq ref_res opt_res

let prim_root_powers =
  let n = NewHope_param.n in
  let powers = Array.init (n/2) (fun _ -> 1) in
  for i = 1 to (Array.length powers - 1) do
    powers.(i) <- (powers.(i - 1) * NewHope_param.omega) mod NewHope_param.q
  done;
  powers

let test_mul_mod =
  let x = mk_const_s ctx "x" bits in
  Array.iter (fun root ->
      Printf.printf "Verify_Eqing with y = %d\n" root; flush_all ();
      let y = const root in
      let y_mont = mk_extract ctx 15 0 (mk_urem ctx (mk_mul ctx (to_u32 y) (const_32 65536)) (const_32 NewHope_param.q)) in
      let ref_res = mul_red_ref x y in
      let opt_res = montgomery_multiply_reduce x y_mont in
      verify_eq ref_res opt_res)
    prim_root_powers
