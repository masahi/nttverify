(* open Tagless_types *)

module R = struct
  type 'a expr = unit -> 'a
  type 'a stmt = unit -> 'a
  type ('a, 'b) func_rep = ('a -> 'b) expr
  type ('a1, 'a2, 'b) func_rep2 = ('a1 -> 'a2 -> 'b) expr

  let int_ n = fun () -> n

  let shift_l a b =
    fun () ->
    Int.shift_left (a ()) (b ())

  let shift_r a b =
    fun () ->
    Int.shift_right (a ()) (b ())

  let (%+) x y = fun () -> x () + y ()
  let (%-) x y = fun () -> x () - y ()
  let (%*) x y = fun () -> x () * y ()
  let (%/) x y = fun () -> x () / y ()
  let (%<) x y = fun () -> x () < y ()

  let mulhi x y =
    let x = x () in
    let y = y () in
    let prod = x * y in
    fun () -> Int.shift_right_logical prod 16

  let mullo x y =
    let x = x () in
    let y = y () in
    let prod = x * y in
    fun () -> prod mod (Int.shift_left 1 16)

  let not_zero x =
    fun () -> Bool.to_int (x () != 0)

  let (%<<) a b = fun () -> Int.shift_left (a ()) (b ())
  let (%>>) a b = fun () -> Int.shift_right (a ()) (b ())

  let (%&) x y = fun () -> x () land y ()

  let func _ _ f = fun () -> (fun a -> (f (fun () -> a)) ())
  let func2 _ _ _ f = fun () -> (fun a1 a2 -> (f (fun () -> a1) (fun () -> a2)) ())


  let app f arg =
    fun () -> (f ()) (arg ())

  let app2 f arg1 arg2 =
    fun () -> (f ()) (arg1 ()) (arg2 ())

  let new_var v k =
    let var = ref (v ()) in
    k (fun () -> var)

  let asgn var v =
    let var = var () in
    let v = v () in
    fun () -> var := v

  let deref var = fun () -> !(var ())

  let return_ v =
    fun () -> v ()

  let if_ cond tru fls =
    fun () ->
    if cond () then
      tru ()
    else begin
      match fls with
      | Some stmt -> stmt ()
      | _ -> ()
    end

  let let_ rhs body =
    let r = rhs () in
    body (fun () -> r)

  let for_ low high step body =
    fun () ->
    let num_iter = (high () - low ()) / (step ())in
    let index = ref (low ()) in
    for _ = 0 to num_iter - 1 do
      body (fun () -> !index) ();
      index := !index + (step ())
    done

  let for_step = 1

  let seq s1 s2 = fun () -> ignore(s1 ()); s2 ()

  let ignore_ e = fun () -> ignore(e ())
end

module R_complex = struct
  include R
  let complex_ v = fun () -> v

  let cadd x y = fun () -> Complex.add (x ()) (y ())
  let csub x y = fun () -> Complex.sub (x ()) (y ())
  let cmul x y = fun () -> Complex.mul (x ()) (y ())
end

module R_Array = struct
  include R
  type 'a arr = 'a array

  let arr_init n f =
    let a = Array.init n (fun i -> (f i) ()) in
    fun () -> a

  let arr_length arr =
    let len = Array.length (arr ()) in
    fun () -> len

  let arr_copy arr =
    fun () -> Array.copy (arr ())

  let arr_get arr i =
    let arr = arr () in
    let i = i () in
    let v = arr.(i) in
    fun () -> v

  let arr_set arr i v =
    let arr = arr () in
    let i = i () in
    let v = v () in
    fun () ->
      arr.(i) <-  v

end

module R_modulo = struct
  include R
  let mod_ a b = fun () -> a () mod b
end

module R_aux = struct
  include R

  (* module Int_aux(T: sig type t val c_ty: t c_type end) = struct
   *   type t = T.t
   *   type 'a expr = 'a c_type * string
   *
   *   let (%+) x y = x () + y ()
   *   let (%-) (_, x) (_, y) = (T.c_ty, sprintf "(%s - %s)" x y)
   *   let (%*\) (_, x) (_, y) = (T.c_ty, sprintf "(%s * %s)" x y)
   *   let (%&) (_, x) (_, y) = (T.c_ty, sprintf "(%s & %s)" x y)
   *   let (%<<) (_, a) b = (T.c_ty, sprintf "(%s << %d)" a b)
   *   let (%>>) (_, a) b = (T.c_ty, sprintf "(%s >> %d)" a b)
   * end
   *
   * module Int16 = struct
   *   include Int_aux(struct type t = int16 let c_ty = CInt16 end)
   *
   *   let to_uint16 (_, v) =
   *     CUInt16, sprintf "(uint16_t)%s" v
   *
   *   let lift v = (CInt16, sprintf "%d" (Signed.Int32.to_int v))
   * end *)

  (* module UInt16 = struct
   *   include Int_aux(struct type t = uint16 let c_ty = CUInt16 end)
   *
   *   let to_int16 (_, v) =
   *     CInt16, sprintf "(int16_t)%s" v
   *
   *   let to_uint32 (_, v) =
   *     CUInt32, sprintf "(uint32_t)%s" v
   *
   *   let lift v = (CUInt16, sprintf "%d" (Unsigned.UInt16.to_int v))
   * end
   *
   * module UInt32 = struct
   *   include Int_aux(struct type t = uint32 let c_ty = CUInt32 end)
   *
   *   let to_uint16 (_, v) =
   *     CUInt16, sprintf "(uint16_t)%s" v
   *
   *   let lift v = (CUInt32, sprintf "%d" (Unsigned.UInt32.to_int v))
   * end *)


end
