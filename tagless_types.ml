type z = Z and _ s = S

type _ nat = Z : z nat | S : 'n nat -> 'n s nat

(* ('a, n) vec = a vector of length 2^n *)
type ('a, _) vec =
  | Scalar : 'a -> ('a, z) vec
  | Combine : ('a, 'n) vec * ('a, 'n) vec -> ('a, 'n s) vec


type _ c_type = ..

type _ c_type +=
  | CVoid: unit c_type
  | CBool: bool c_type
  (* |( CInt32: Signed.Int32.t c_type *)
  | CInt: int c_type (* TODO: replace with above *)
  | CInt16: Signed.Int32.t c_type (* Int16 doesnt exist *)
  | CUInt16: Unsigned.UInt16.t c_type
  | CUInt32: Unsigned.UInt32.t c_type
  | CRef: 'a c_type -> 'a ref c_type
  | CArr: 'a c_type -> 'a array c_type
  | CVec: 'a c_type * 'n nat -> ('a, 'n) vec c_type

let rec nat_to_int: type n. n nat -> int = function
  | Z -> 0
  | S(n) -> 1 + (nat_to_int n)

let rec pow a = function
  | 0 -> 1
  | 1 -> a
  | n ->
    let b = pow a (n / 2) in
    b * b * (if n mod 2 = 0 then 1 else a)

let nat_to_elem_width n =
  let i = nat_to_int n in
  pow 2 i


let rec ty_to_ty_str : type a. a c_type -> string = function
  | CVoid -> "void"
  | CBool -> "bool"
  | CInt -> "int"
  | CRef inner_ty -> (ty_to_ty_str inner_ty)
  | CArr inner_ty -> Printf.sprintf "%s*" (ty_to_ty_str inner_ty)
  | CInt16 -> "int16_t"
  | CUInt16 -> "uint16_t"
  | CUInt32 -> "uint32_t"
  | CVec (scalar_ty, n) ->
    begin match scalar_ty, nat_to_elem_width n with
    | CUInt16, 16 -> "__m256i"
    | CInt16, 16 -> "__m256i"
    | CUInt16, 32 -> "__m512i"
    | CInt16, 32 -> "__m512i"
    | CUInt32, 8 -> "__m256i"
    | CUInt32, 16 -> "__m512i"
    | _ -> "not supported yet"
    end
  | _ -> "?"


module type C_lang = sig
  type 'a expr
  type 'a stmt
  type ('a, 'b) func_rep
  type ('a1, 'a2, 'b) func_rep2

  val int_ : int -> int expr   (* constant *)

  val (%+) : int expr -> int expr -> int expr
  val (%-) : int expr -> int expr -> int expr
  val (%*) : int expr -> int expr -> int expr
  val (%/) : int expr -> int expr -> int expr
  val (%&) : int expr -> int expr -> int expr
  val (%<) : int expr -> int expr -> bool expr
  val (%<<) : int expr -> int expr -> int expr
  val (%>>) : int expr -> int expr -> int expr

  val func : string -> 'a c_type -> ('a expr -> 'b stmt) -> ('a, 'b) func_rep
  val func2 : string -> 'a1 c_type -> 'a2 c_type -> ('a1 expr -> 'a2 expr -> 'b stmt) -> ('a1, 'a2, 'b) func_rep2
  val app : ('a, 'b) func_rep -> 'a expr -> 'b expr
  val app2 : ('a1, 'a2, 'b) func_rep2 -> 'a1 expr -> 'a2 expr -> 'b expr

  val if_  : bool expr -> unit stmt -> unit stmt option  -> unit stmt

  val for_ : int expr -> int expr -> int expr -> (int expr -> unit stmt) -> unit stmt
  val for_step: int

  (* this is for generating let without reference *)
  val let_ : 'a expr -> ('a expr -> 'r stmt) -> 'r stmt

  val return_ : 'r expr -> 'r stmt
  val seq : 'a stmt -> 'b stmt -> 'b stmt

  val ignore_: 'a expr -> unit stmt
end

module type Arith = sig
  type t
  type 'a expr
  val lift: t -> t expr
  val (%+): t expr -> t expr -> t expr
  val (%-): t expr -> t expr -> t expr
  val (%*): t expr -> t expr -> t expr
  val (%&): t expr -> t expr -> t expr
  val (%<<): t expr -> int -> t expr
  val (%>>): t expr -> int -> t expr
end

module type C_lang_aux = sig
  include C_lang

  type int16 = Signed.Int32.t
  type uint16 = Unsigned.UInt16.t
  type uint32 = Unsigned.UInt32.t

  module Int16: sig
    include (Arith with type t = int16 with type 'a expr = 'a expr)
    val to_uint16: int16 expr -> uint16 expr
  end

  module UInt16: sig
    include (Arith with type t = uint16 with type 'a expr = 'a expr)
    val to_uint32: uint16 expr -> uint32 expr
    val to_int16: uint16 expr -> int16 expr
  end

  module UInt32: sig
    include (Arith with type t = uint32 with type 'a expr = 'a expr)
    val to_uint16: uint32 expr -> uint16 expr
  end
end

module Sugar(L: C_lang) = struct
  open L

  let zero = int_ 0
  let one = int_ 1
  let two = int_ 2

  let call f arg =
    ignore_ (app f arg)

  let call2 f arg1 arg2 =
    ignore_ (app2 f arg1 arg2)

  let seq3 s1 s2 s3 = seq s1 (seq s2 s3)

  let seq4 s1 s2 s3 s4 = seq s1 (seq3 s2 s3 s4)

  let let2 rhs1 rhs2 body =
    let_ rhs1 (fun v1 ->
        let_ rhs2 (fun v2 ->
            body v1 v2))

  let let2_ (rhs1, rhs2) body = let2 rhs1 rhs2 body

  let rec unroll i unroll_end body =
    if i = unroll_end - 1 then body i
    else
      seq
        (body i)
        (unroll (i + 1) unroll_end body)

end

module type Array_lang = sig
  include C_lang
  type 'a arr = 'a array

  val arr_init: int -> (int -> 'a expr) -> 'a arr expr
  val arr_get: 'a arr expr -> int expr -> 'a expr
  val arr_set: 'a arr expr -> int expr -> 'a expr -> unit stmt
end

module type Complex_lang = sig
  include C_lang
  val complex_ : Complex.t -> Complex.t expr   (* constant *)
  val cadd : Complex.t expr -> Complex.t expr -> Complex.t expr
  val csub : Complex.t expr -> Complex.t expr -> Complex.t expr
  val cmul : Complex.t expr -> Complex.t expr -> Complex.t expr
end

module type Int_modulo_lang = sig
  (* to access prim_roots table, array interface is needed *)
  include C_lang
  val mod_ : int expr -> int -> int expr
end

module type Int_lang_for_reduction = sig
  (* to access prim_roots table, array interface is needed *)
  include C_lang
  val mulhi: int expr -> int expr -> int expr
  val mullo: int expr -> int expr -> int expr

  val not_zero: int expr -> int expr
end

module type C_lang_aux_for_reduction = sig
  (* to access prim_roots table, array interface is needed *)
  include C_lang_aux
  val mulhi: int expr -> int expr -> int expr
  val mullo: int expr -> int expr -> int expr

  val not_zero: int expr -> int expr
end

module type Domain = sig
  type 'a expr
  type t

  val domain_c_type: t c_type

  val lift: t -> t expr
  val add: t expr -> t expr -> t expr
  val sub: t expr -> t expr -> t expr
  val mul: t expr -> t expr -> t expr

  val one: t

  val primitive_root_power: int -> int -> t
end

module type Vectorized_domain = sig
  type 'a expr
  type 'a vec
  type t

  val vadd: t vec expr -> t vec expr-> t vec expr
  val vsub: t vec expr -> t vec expr-> t vec expr
  val vmul: t vec expr -> t vec expr-> t vec expr
end

module type Vector_lang = sig
  include Array_lang
  module Vector_domain: Vectorized_domain with type 'a expr = 'a expr

  type 'a vec = 'a Vector_domain.vec
  val vec_len: int
  (* val broadcast : 'a expr -> 'a vec expr *)
  val vload: 'a arr expr -> int expr -> 'a vec expr
  val vstore: 'a arr expr -> int expr -> 'a vec expr -> unit stmt
end

module type Vector_lang_with_shuffle = sig
  include Vector_lang
  type t = Vector_domain.t
  type 'a vec = 'a Vector_domain.vec
  val shuffle: int -> t vec expr -> t vec expr -> (t vec expr * t vec expr)
end

module type Vector_lang_with_shuffle_with_barret = sig
  include Vector_lang_with_shuffle
  type t = Vector_domain.t
  type 'a vec = 'a Vector_domain.vec
  val barret_reduce: t vec expr -> t vec expr
end

module type Domain_with_barret = sig
  include Domain
  val barret_reduce: t expr -> t expr
end
