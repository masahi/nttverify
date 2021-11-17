open Fft_domain

module DFT(D: Domain) = struct
  module Prim_roots = Primitive_roots(D)
  let dft input =
    let n = Array.length input in
    let dot xs ys = Array.fold_left (fun acc (x, y) -> D.add acc (D.mul x y))
        D.zero (Array.map2 (fun x y -> (x, y)) xs ys) in
    Array.init n (fun i ->
        let coeffs = Prim_roots.powers n n i in
        dot input coeffs)
end
