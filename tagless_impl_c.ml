open Printf
open Tagless_types

module C_codegen = struct
  type 'a expr = 'a c_type * string
  type 'a stmt = 'a c_type * string
  type 'a arr = 'a array

  type ('a, 'b) func_rep = 'a c_type * 'b c_type * string
  type ('a1, 'a2, 'b) func_rep2 = 'a1 c_type * 'a2 c_type * 'b c_type * string

  let fresh_var =
    let c = ref 0 in
    fun () ->
      let current = !c in
      c := !c + 1;
      sprintf "v_%d" current

  let int_ n = (CInt, sprintf "%d" n)
  let mod_ (_, n) q = (CInt, sprintf "(%s %c %d)" n '%' q)

  let (%+) (_, x) (_, y) = (CInt, sprintf "(%s + %s)" x y)
  let (%-) (_, x) (_, y) = (CInt, sprintf "(%s - %s)" x y)
  let (%*) (_, x) (_, y) = (CInt, sprintf "(%s * %s)" x y)
  let (%/) (_, x) (_, y) = (CInt, sprintf "(%s / %s)" x y)
  let (%<) (_, x) (_, y) = (CBool, sprintf "(%s < %s)" x y)
  let (%&) (_, x) (_, y) = (CInt, sprintf "(%s & %s)" x y)
  let (%<<) (_, a) (_, b) = (CInt, sprintf "(%s << %s)" a b)
  let (%>>) (_, a) (_, b) = (CInt, sprintf "(%s >> %s)" a b)

  let mullo (_, x) (_, y) = (CInt, sprintf "(((uint32_t)%s * (uint32_t)%s) %c (1 << 16))" x y '%')
  let mulhi (_, x) (_, y) = (CInt, sprintf "(((uint32_t)%s * (uint32_t)%s) %c (1 << 16))" x y '/')
  let not_zero (_, x) = (CInt, sprintf "%s > 0" x)

  let default_headers = ["stdint.h"; "immintrin.h"]

  let init_decls () =
    let headers = List.map (fun header -> ("", sprintf "#include <%s>" header)) default_headers in
    List.append headers [("", "")] (* just for adding newline between the last header and function decls *)

  let decls = ref (init_decls ())

  let clear_decls () =
    decls := init_decls ()

  let indent_level = ref 0

  let get_declaration () =
    List.map (fun (_, decl) -> decl) !decls |> List.fold_left (fun acc decl -> acc ^ "\n" ^ decl) ""

  let with_indent str =
    let indent = String.init (2 * !indent_level) (fun _ -> ' ') in
    indent ^ str

  let func: type a. string -> a c_type -> (a expr -> 'b stmt) -> (a, 'b) func_rep =
    fun fn_name arg_type f ->
    let arg_str = "arg0" in
    indent_level := !indent_level + 1;
    let (ret_ty, body) = f (arg_type, arg_str) in
    let decl = sprintf "%s %s(%s %s) {\n%s}\n" (ty_to_ty_str ret_ty) fn_name (ty_to_ty_str arg_type) arg_str body in
    indent_level := !indent_level - 1;
    let _ =
      try
        ignore(List.assoc fn_name !decls)
      with
      | Not_found ->
        decls := List.append !decls [(fn_name, decl)]
    in
    arg_type, ret_ty, fn_name

  (* TODO: clean *)
  let func2: type a1 a2. string -> a1 c_type -> a2 c_type -> (a1 expr -> a2 expr -> 'b stmt) -> (a1, a2, 'b) func_rep2 =
    fun fn_name arg_type1 arg_type2 f ->
    let arg_str1 = "arg0" in
    let arg_str2 = "arg1" in
    indent_level := !indent_level + 1;
    let (ret_ty, body) = f (arg_type1, arg_str1) (arg_type2, arg_str2) in
    let arg_string = sprintf "%s %s, %s %s" (ty_to_ty_str arg_type1) arg_str1 (ty_to_ty_str arg_type2) arg_str2 in
    let decl = sprintf "%s %s(%s) {\n%s}\n" (ty_to_ty_str ret_ty) fn_name arg_string body in
    indent_level := !indent_level - 1;
    let _ =
      try
        ignore(List.assoc fn_name !decls)
      with
      | Not_found ->
        decls := List.append !decls [(fn_name, decl)]
    in
    arg_type1, arg_type2, ret_ty, fn_name

  let app (_, ret_ty, f_name) (_, arg_str) =
    ret_ty, sprintf "%s(%s)" f_name arg_str

  let app2 (_, _, ret_ty, f_name) (_, arg_str1) (_, arg_str2) =
    ret_ty, sprintf "%s(%s, %s)" f_name arg_str1 arg_str2

  let asgn (_, var) (_, v) =
    CVoid, with_indent (sprintf "%s = %s;\n" var v)

  let deref: type a. (a ref c_type * string) -> (a c_type * string) =
    fun (ref_ty, str) -> match ref_ty with
      | CRef ty -> ty, str
      | _ -> assert false (*Ctype unsigned integer, which is private*)

  let return_ (ty, v) =
    ty, with_indent (sprintf "return %s; \n" v)

  let if_ (_, cond) (ty, tru) fls_opt =
    let more_indent block =
      let stmts = String.split_on_char '\n' block |>
                  List.map (fun stmt -> if String.length stmt == 0 then "" else  "  " ^ stmt) in
      String.concat "\n" stmts in
    let then_block = with_indent (sprintf "if (%s) {\n%s%s}\n" cond (more_indent tru) (with_indent "")) in
    let else_block = match fls_opt with
      | Some (_, fls) ->
        let (template_els: _ format) =
          "else {\n%s%s}\n" in
        with_indent (sprintf template_els (more_indent fls) (with_indent ""))
      | None -> ""
    in
    (ty, then_block ^ else_block)


  let let_common rhs_c_ty rhs_val body_arg_ty body =
    let typ_str = ty_to_ty_str rhs_c_ty in
    if typ_str = "void" then
      let stmt = with_indent (sprintf "%s;\n" rhs_val) in
      let (body_typ, body_str) = body (body_arg_ty, "") in
      body_typ, (stmt ^ body_str)
    else
      let var_name = fresh_var () in
      let var_decl_str = with_indent (sprintf "%s %s = %s;\n" typ_str var_name rhs_val) in
      let (body_typ, body_str) = body (body_arg_ty, var_name) in
      body_typ, (var_decl_str ^ body_str)

  let let_: 'a expr -> ('a expr -> 'r stmt) -> 'r stmt = fun (c_ty, val_str) body ->
    let_common c_ty val_str c_ty body

  let new_var: 'a expr -> ('a ref expr -> 'r stmt) -> 'r stmt =  fun (c_ty, val_str) body ->
    let_common c_ty val_str (CRef c_ty) body

  let for_ (_, low) (_, high) (_, step) body =
    let var_name = fresh_var () in
    let loop_str = with_indent (sprintf "for (int %s = %s; %s < %s; %s += %s)" var_name low var_name high var_name step) in
    indent_level := !indent_level + 1;
    let (_, body_str) = body (CInt, var_name) in
    indent_level := !indent_level - 1;
    CVoid,  loop_str ^ (sprintf " {\n%s%s} \n" body_str (with_indent ""))

  let seq (_, s1) (ty, s2) = ty, sprintf "%s%s" s1 s2

  let arr_init: type a. int -> (int -> (a c_type * string)) -> (a array c_type * string) = fun size init_fun ->
    assert (size > 1);
    let elements = Array.init size (fun i -> init_fun i) in
    let (elem_ty, elem_head) = elements.(0) in
    let elements_tail = Array.init (size - 1) (fun i -> let (_, elem) = elements.(i + 1) in elem) in
    let elements_str = Array.fold_left (fun acc elem -> acc ^ ", " ^ elem) elem_head elements_tail in
    let ty_str = ty_to_ty_str elem_ty in
    let var_name = fresh_var () in
    let arr_decl = sprintf "%s %s[%d] = {%s};\n" ty_str var_name size elements_str in
    decls := List.append !decls [(var_name, arr_decl)];
    CArr elem_ty, var_name

  let arr_get: type a. (a array c_type * string) -> (int c_type * string) -> (a c_type * string) =
    fun (arr_ty, arr) (_, ind) -> match arr_ty with
      | CArr(scalar_ty) ->  (scalar_ty, sprintf "%s[%s]" arr ind)
      | _ -> assert false (*Ctype integer, which is private*)

  let arr_set: type a. (a array c_type * string) -> (int c_type * string) -> (a c_type * string) -> (unit c_type * string) =
    fun (_, arr) (_, ind) (_, v) -> (CVoid, with_indent (sprintf "%s[%s] = %s;\n" arr ind v))

  let for_step = 1

  let ignore_ v = let_ v (fun _ -> (CVoid, ""))

  type int16 = Signed.Int32.t
  type uint16 = Unsigned.UInt16.t
  type uint32 = Unsigned.UInt32.t

  module Int_aux(T: sig type t val c_ty: t c_type end) = struct
    type t = T.t
    type 'a expr = 'a c_type * string

    let (%+) (_, x) (_, y) = (T.c_ty, sprintf "(%s + %s)" x y)
    let (%-) (_, x) (_, y) = (T.c_ty, sprintf "(%s - %s)" x y)
    let (%*) (_, x) (_, y) = (T.c_ty, sprintf "(%s * %s)" x y)
    let (%&) (_, x) (_, y) = (T.c_ty, sprintf "(%s & %s)" x y)
    let (%<<) (_, a) b = (T.c_ty, sprintf "(%s << %d)" a b)
    let (%>>) (_, a) b = (T.c_ty, sprintf "(%s >> %d)" a b)
  end

  module Int16 = struct
    include Int_aux(struct type t = int16 let c_ty = CInt16 end)

    let to_uint16 (_, v) =
      CUInt16, sprintf "(uint16_t)%s" v

    let lift v = (CInt16, sprintf "%d" (Signed.Int32.to_int v))
  end

  module UInt16 = struct
    include Int_aux(struct type t = uint16 let c_ty = CUInt16 end)

    let to_int16 (_, v) =
      CInt16, sprintf "(int16_t)%s" v

    let to_uint32 (_, v) =
      CUInt32, sprintf "(uint32_t)%s" v

    let lift v = (CUInt16, sprintf "%d" (Unsigned.UInt16.to_int v))
  end

  module UInt32 = struct
    include Int_aux(struct type t = uint32 let c_ty = CUInt32 end)

    let to_uint16 (_, v) =
      CUInt16, sprintf "(uint16_t)%s" v

    let lift v = (CUInt32, sprintf "%d" (Unsigned.UInt32.to_int v))
  end

end

module type Vec_spec = sig
  type t
  type n
end

module type Arith_instruction = sig
  include Vec_spec
  val vadd: string
  val vsub: string
  val vmullo: string
end

module type Mem_instruction = sig
  include Vec_spec

  val vec_len_exponent: n nat

  val vload: string
  val vstore: string
end


module Integer_SIMD(Instr: Arith_instruction) = struct
  type t = Instr.t
  type 'a expr = 'a c_type * string
  type 'a vec = ('a, Instr.n) Tagless_types.vec

  let binop: string -> t vec expr -> t vec expr-> t vec expr = fun op (ty1, v1) (ty2, v2) ->
    match ty1, ty2 with
    | CVec(_, _), CVec(_, _) ->
      (ty1, sprintf "%s(%s, %s)" op v1 v2)
    | _ -> assert false

  let vadd = binop Instr.vadd
  let vsub = binop Instr.vsub
  let vmul = binop Instr.vmullo
end

module SIMD_Mem(Instr: Mem_instruction) = struct
  open C_codegen
  type 'a vec = ('a, Instr.n) Tagless_types.vec

  let vload: 'a arr expr -> int expr -> 'a vec expr = fun (arr_ty, src) (_, index) ->
    match arr_ty with
    | CArr(scalar_ty) ->
      let vec_ty = CVec (scalar_ty, Instr.vec_len_exponent) in
      let vec_ty_str = ty_to_ty_str vec_ty in
      (vec_ty, sprintf "%s((%s*)(%s + %s))" Instr.vload vec_ty_str src index)
    | _ -> assert false (*Ctype integer, which is private*)

  let vstore: 'a arr expr -> int expr -> 'a vec expr -> unit stmt =
    fun (_, src) (_, index) (vec_ty, v) ->
    let vec_ty_str = ty_to_ty_str vec_ty in
    (CVoid, with_indent (sprintf "%s((%s*)(%s + %s), %s);\n" Instr.vstore vec_ty_str src index v))
end

module AVX2_UInt16(Scalar_domain: Domain) = struct
  include C_codegen
  type four = z s s s s
  type t = Scalar_domain.t

  let vec_len = 16

  module Vec16U16 = struct
    type t = Scalar_domain.t
    type n = four
  end

  module Mem = struct
    include Vec16U16
    let vec_len_exponent = S (S (S (S Z)))

    let vload = "_mm256_loadu_si256"
    let vstore = "_mm256_storeu_si256"
  end

  include SIMD_Mem(Mem)

  module Arith = struct
    include Vec16U16

    let vadd = "_mm256_add_epi16"
    let vsub = "_mm256_sub_epi16"

    let vmullo = "_mm256_mullo_epi16"
  end

  module Vector_domain = Integer_SIMD(Arith)
end
