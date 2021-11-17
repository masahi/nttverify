open Ctypes
open Foreign
open Tagless_fft
open Tagless_impl_c

let get_prim_root n q =
  assert (n = 1024 && q = 12289);
  49

let get_wrapper_common out_so func_name signature =
  let dl_path = Printf.sprintf "/home/masa/projects/dev/nttgen/%s" out_so in
  let dl = Dl.dlopen ~flags:[Dl.RTLD_LAZY] ~filename:dl_path in
  foreign func_name ~from:dl signature

let get_wrapper out_so func_name arg_ty ret_ty =
  get_wrapper_common out_so func_name (arg_ty @-> returning ret_ty)

let get_wrapper2 out_so func_name arg_ty1 arg_ty2 ret_ty =
  get_wrapper_common out_so func_name (arg_ty1 @-> arg_ty2 @-> returning ret_ty)

let compile_c decls out_so =
  let tmp_c = Printf.sprintf "%s.c" out_so in
  let oc = open_out tmp_c in
  Printf.fprintf oc "%s" decls;
  close_out oc;
  (* ignore(decls); *)
  let format_command = Printf.sprintf "clang-format -i %s" tmp_c in
  (* let command = Printf.sprintf "clang-11 -O3 -mavx2 -mavx512bw -mavx512f -shared %s -fPIC -o %s" tmp_c out_so in *)
  let command = Printf.sprintf "clang -O3 -mavx2 -shared %s -fPIC -o %s" tmp_c out_so in
  (* let command = Printf.sprintf "clang -O3 -mavx2 -shared %s -fPIC -o %s" "for_frama2.c" out_so in *)
  ignore(Sys.command format_command);
  ignore(Sys.command command);
  C_codegen.clear_decls ()

let get_ntt_uint16 (module Param: Ntt_param) =
  let module C_Int_mod = UIntegerModulo_lazy(C_codegen)(Param) in
  let module C_NTT = FFT_lazy_gen(C_codegen)(C_Int_mod) in
  (* let module SIMD = Vector_newhope.AVX2_UInt16_int_modulo_with_shuffle(C_Int_mod)(Param) in
   * (\* let module SIMD = Vector_newhope.AVX512_UInt16_int_modulo_with_shuffle(C_Int_mod)(Param) in *\)
   * let module C_NTT = FFT_vectorized_with_shuffle_gen(C_codegen)(C_Int_mod)(SIMD) in *)
  let (_, _, fn_name) = C_NTT.fft Param.n in
  let decls = C_codegen.get_declaration () in
  let out_so = "generated_u16.so" in
  compile_c decls out_so;
  get_wrapper out_so fn_name (ptr uint16_t) void

let test_ntt_uint16 =
  let size = 1024 in
  let q = 12289 in
  let qinv = 12287 in
  let omega = get_prim_root size q in
  let module Param = struct let q = q let qinv = qinv let omega = omega let n = size end in
  let ntt = get_ntt_uint16 (module Param) in
  let bounds = Interval_abstract.get_output_bounds size in
  let open Dft in
  let open DFT(Fft_types.IntegerModulo(Param)) in
  for i = 1 to 10 do
    ignore(i);
    let arr = Array.init size (fun _ -> Random.int Param.q) in
    let ref_res = dft arr in
    let in_arr = CArray.of_list uint16_t (List.init size (fun i -> Unsigned.UInt16.of_int arr.(i))) in
    ntt (CArray.start in_arr);
    ignore(Array.init size (fun i ->
        let res = Unsigned.UInt16.to_int (CArray.get in_arr i) in
        assert ((fst bounds.(i)) <= res && res <= (snd bounds.(i)));
        let res = res mod q in
        assert (res == ref_res.(i))))
  done
