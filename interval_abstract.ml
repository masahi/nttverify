open Tagless_impl
open Tagless_interval
open Tagless_fft

module NewHope_param = struct
  let q = 12289

  let qinv = 12287

  let omega = 49

  let n = 1024

end

module Int_mod_interval = IntegerModulo_interval(NewHope_param)

let get_output_bounds size =
  let module R_NTT = FFT_lazy_gen(R_Array)(Int_mod_interval) in
  let open R_Array in
  let arr = (arr_init size (fun _ -> (fun () -> (0, NewHope_param.q - 1)))) () in
  let fn = (R_NTT.fft size) () in
  fn arr;
  arr

let test_ntt_R =
  let size = 1024 in
  let arr = get_output_bounds size in
  ignore(Array.init size (fun i ->
      let lo, hi = arr.(i) in
      Printf.printf "lo = %d, hi = %d\n" lo hi))
