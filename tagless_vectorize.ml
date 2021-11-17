open Tagless_types

module type Vec = sig
  include Array_lang
  type 'a vec

  module D: sig
    type t

    val add: t vec expr -> t vec expr-> t vec expr
    val sub: t vec expr -> t vec expr-> t vec expr
    val mul: t vec expr -> t vec expr-> t vec expr

  end

  (* val broadcast: 'a expr -> 'a vec expr *)

  val arr_get: 'a arr expr -> int expr -> 'a vec expr
  val arr_set: 'a arr expr -> int expr -> 'a vec expr -> unit stmt

  val for_ : int expr -> int expr -> int expr -> (int expr -> unit stmt)
    -> unit stmt

end

module Scalarize(Base_lang: Array_lang)(D_scalar: Domain with type 'a expr = 'a Base_lang.expr) : Vec
  with type 'a expr = 'a Base_lang.expr
  with type 'a stmt = 'a Base_lang.stmt
  with type 'a arr = 'a Base_lang.arr
  with type D.t = D_scalar.t = struct

  include Base_lang
  type 'a vec = 'a

  module D = D_scalar

  (* let broadcast v = v *)

end

module Vectorize_domain_emu(Base_lang: Array_lang)(D: Domain with type 'a expr = 'a Base_lang.expr) = struct
  module D_scalar = D
  include Base_lang

  type t = D.t
  type 'a vec = 'a arr

  let vec_len = 16

  let binop op vec1 vec2 = arr_init vec_len (fun i -> op (arr_get vec1 (int_ i)) (arr_get vec2 (int_ i)))
  let vadd = binop D.add
  let vsub = binop D.sub
  let vmul = binop D.mul
end


module Vectorize_lang_emu(Base_lang: Array_lang)(D: Domain with type 'a expr = 'a Base_lang.expr) = struct
  include Base_lang
  type 'a vec = 'a arr

  module Vector_domain = Vectorize_domain_emu(Base_lang)(D)

  let vec_len = 16

  (* let broadcast v =
   *   arr_init vec_len (fun _ -> v) *)

  let vload arr ind =
    arr_init vec_len (fun i -> Base_lang.arr_get arr (ind %+ (int_ i)))

  let vstore arr ind v =
    for_ (int_ 0) (int_ vec_len) (int_ 1) (fun i ->
        arr_set arr (ind %+ i) (Base_lang.arr_get v i))

end

module Vectorize(Base_lang: Vector_lang): Vec
  with type 'a expr = 'a Base_lang.expr
  with type 'a stmt = 'a Base_lang.stmt
  with type 'a arr = 'a Base_lang.arr
  with type D.t = Base_lang.Vector_domain.t = struct

  module Vec_D = Base_lang.Vector_domain

  include Base_lang
  type 'a vec = 'a Vec_D.vec

  let vec_len = Base_lang.vec_len
  let for_step = vec_len

  module D = struct
    type t = Vec_D.t

    let add = Vec_D.vadd
    let sub = Vec_D.vsub
    let mul = Vec_D.vmul
  end

  (* let broadcast = Base_lang.broadcast *)

  let arr_get = Base_lang.vload

  let arr_set = Base_lang.vstore

  let for_ lo hi _ body =
    let num_loop = (hi %- lo) %/ (int_ vec_len) in
    Base_lang.for_ (int_ 0) num_loop (int_ 1) (fun i ->
        body (lo %+ (i %* (int_ vec_len))))
end
