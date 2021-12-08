module type Domain =
sig
  type t
  val add : t -> t -> t
  val sub : t -> t -> t
  val mul : t -> t -> t
  val zero: t
  val one: t
  val primitive_root_power : int -> int -> t
end

module Primitive_roots(D: Domain) = struct
  let powers n num_powers init_power =
    let prim_root = D.primitive_root_power n init_power in
    let powers = Array.make num_powers D.one in
    for i = 1 to (num_powers - 1) do
      powers.(i) <- D.mul powers.(i-1) prim_root
    done;
    powers

  let powers_memory_efficient n =
    let num_stage = Base.Int.floor_log2 n in
    let powers = Array.make n D.one in
    let index = ref 0 in
    for s = 1 to num_stage do
      let m = Int.shift_left 1 s in
      let num_butterfly = Int.shift_right n s in
      for j = 0 to (m / 2 - 1) do
        powers.(!index) <- D.primitive_root_power n (j * num_butterfly);
        index := !index + 1;
      done;
    done;
    powers
end
