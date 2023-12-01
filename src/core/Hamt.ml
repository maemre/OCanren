(* Hash-array mapped tries.  The interface matches what is provided by OCaml's
   Map module. *)

let (%) f g x = f (g x)

module type S = sig
  type key
  type !'v t

  val empty: 'v t

  val add: key -> 'v -> 'v t -> 'v t
  val remove: key -> 'v t -> 'v t
  val find: key -> 'v t -> 'v
  val mem: key -> 'v t -> bool
  val update: key -> ('v option -> 'v option) -> 'v t -> 'v t

  (* generic collection methods *)
  val fold : (key -> 'v -> 'acc -> 'acc) -> 'v t -> 'acc -> 'acc
  val for_all: (key -> 'v -> bool) -> 'v t -> bool
  val choose : 'v t -> (key * 'v)
  val choose_opt : 'v t -> (key * 'v) option
  val is_empty : 'v t -> bool
  val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t

  (* print the trie for debugging *)
  val dbg : (key -> string) -> 'v t -> string
end

module type HashedType = Hashtbl.HashedType

let todo _ = failwith "not implemented yet"
let uncurry f (x, y) = f x y
let curry f x y = f (x, y)


module List = Stdlib.List

module Make (H: HashedType) (O: Map.OrderedType with type t = H.t) : S with type key = H.t = struct
  type key = H.t

  module Bucket = Array

  type !'v bucket = (key * 'v) list
  
  type !'v node = CNode of ('v cnode)
               | BNode of ('v bnode)
               | Empty (* to get around value restriction *)
  and !'v bnode = (('v node) option) Bucket.t
  and !'v cnode = ('v bucket * int)

  type !'v t = 'v node

  (* bucket size parameters *)
  let key_segment_size = 6
  let bucket_size = 1 lsl key_segment_size
  let bucket_mask = bucket_size - 1

  let empty_bnode (): ('v node option) array = Bucket.make bucket_size None
  let empty : 'v node = Empty

  (* let rec insert_at xs n x = match (xs, n) with *)
  (*   | _ when n < 0 -> failwith "called with negative index!" *)
  (*   | (_ :: rest, 0) -> Some x :: rest  *)
  (*   | (h :: rest, n) -> h :: insert_at rest (n - 1) x *)
  (*   | ([], _) -> failwith "n >= length of the list" *)

  let insert_at arr i x = let arr = Bucket.copy arr in Bucket.set arr i (Some x); arr

  (* Create a trie that distinguishes hash1 and hash2, and each hash should contain the associated bucket *)
  let make_trie (hash1, bucket1 : int * 'v bucket) (hash2, bucket2) : 'v bnode = begin
      assert (hash1 != hash2);
      let rec inner (hash1, bucket1) (hash2, bucket2) =
        let segment1 = hash1 land bucket_mask
        and segment2 = hash2 land bucket_mask
        and rest_of_hash1 = hash1 lsr key_segment_size
        and rest_of_hash2 = hash2 lsr key_segment_size
        in
        if segment1 < segment2 then
          inner (hash2, bucket2) (hash1, bucket1)
        else if segment1 == segment2 then
          (* we cannot distinguish the segments, so we need to create more BNodes recursively *)
          insert_at (empty_bnode ()) segment1 @@ BNode (inner (rest_of_hash1, bucket1) (rest_of_hash2, bucket2))
        else
          (* we can distinguish the buckers, so we can create a BNode now *)
          insert_at (insert_at (empty_bnode ()) segment1 @@ CNode(bucket1, rest_of_hash1))
            segment2 @@ CNode(bucket2, rest_of_hash2)
      in inner (hash1, bucket1) (hash2, bucket2)
    end

  let rec update_node k (v : 'v) hash : 'v t -> 'v t = function
    | BNode children ->
       let segment = hash land bucket_mask
       and restOfHash = hash lsr key_segment_size in
       begin
         match Bucket.get children segment with
       | None -> BNode (insert_at children segment (CNode ([(k, v)], restOfHash)))
       | Some child -> BNode (insert_at children segment (update_node k v restOfHash child))
       end 
    | CNode (pairs, h) -> if h == hash then CNode ((k, v) :: List.remove_assoc k pairs, h)
                          else BNode (make_trie (h, pairs) (hash, [(k, v)]))
    | Empty -> update_node k v hash (BNode (empty_bnode ()))

  let rec remove_key k hash : 'v t -> 'v t = function
    | CNode (pairs, h) as node ->
       if h == hash then CNode (List.remove_assoc k pairs, h)
       else node
    | BNode children as node ->
       let segment = hash land bucket_mask
       and restOfHash = hash lsr key_segment_size in
       begin match Bucket.get children segment with
       | None -> node
       | Some child -> BNode (insert_at children segment @@ remove_key k restOfHash child)
       end
    | Empty -> Empty

  let rec find_key k hash = function
    | CNode (pairs, h) when h == hash -> List.assoc k pairs
    | CNode _ -> raise Not_found
    | BNode children ->
       let segment = hash land bucket_mask
       and restOfHash = hash lsr key_segment_size in
       begin match Bucket.get children segment with
       | None -> raise Not_found
       | Some child -> find_key k restOfHash child
       end
    | Empty -> raise Not_found

  let add k v node = update_node k v (H.hash k) node
  let remove k node = remove_key k (H.hash k) node
  let find (k : key) (node : 'v t) : 'v = find_key k (H.hash k) node

  let mem k node = try ignore @@ find k node; true
                   with
                   | Not_found -> false

  let update k f node = match f (try Some (find k node) with Not_found -> None) with
    | Some x -> add k x node
    | None   -> remove k node

  let rec fold f node acc = match node with
    | CNode (pairs, _) -> List.fold_left (Fun.flip @@ uncurry f) acc pairs
    | BNode children ->
       let f' acc : (('v t) option -> 'a) = function
           None -> acc
          |Some node -> fold f node acc
       in Bucket.fold_left f' acc children
    | Empty -> acc
  
  let for_all (p : key -> 'v -> bool) (m : 'v t) : bool = fold ((fun k v rest -> rest && p k v) : 'k -> 'v -> bool -> bool) m true

  let rec choose_opt = function
      | CNode (p :: _, _) -> Some p
      | CNode _ -> None
      | BNode children -> Bucket.to_seq children |> Seq.find_map (fun x -> Stdlib.Option.bind x choose_opt)
      | Empty -> None

  let choose m = Stdlib.Option.get @@ choose_opt m
  let is_empty m = choose_opt m = None

  let union resolve m1 m2 =
    let resolve' k v = update k @@ function
                                  | None -> (Some v)
                                  | Some v' -> resolve k v v'
    in fold resolve' m1 m2

  let to_list m = fold (fun k v xs -> (k, v) :: xs) m []

  (* a really slow implementation, just to pass the tests. *)
  let first_binding m : (key * 'v) = choose m (* to_list m |> List.sort (fun (k1, _) (k2, _) -> O.compare k1 k2) |> List.hd *)

  let rec dbg pp = function
    | CNode (pairs, h) -> Printf.sprintf "(cnode %s %x)" (String.concat "; " @@ List.map (pp % fst) pairs) h
    | BNode children ->
      let f i : 'v t option -> string option = let mk_msg node = Printf.sprintf "(%x %s)" i (dbg pp node)
        in Stdlib.Option.map mk_msg
      in let children_text = Bucket.to_seq children |> Seq.mapi f |> Seq.filter_map Fun.id |> Seq.fold_left (^) ""
      in Printf.sprintf "(bnode %s)" children_text
    | Empty -> "(bnode <empty>)"
   
end

module type Print = sig
  type t
  val pp: t -> string
end

(* HAMT with an intmap inside for debugging. R = Reference map *)
module Debug (H: HashedType) (O: Map.OrderedType with type t = H.t) (P: Print with type t = H.t) : S with type key = H.t = struct

  module Hamt = Make(H)(O)
  module R = Map.Make(O)

  type key = H.t

  type !'v t = 'v Hamt.t * 'v R.t

  exception Consistency_error of string

  let consistency_error msg = raise @@ Consistency_error ("HAMT consistency error: " ^ msg)

  let add_ctx ctx a = try Lazy.force a
    with Consistency_error err -> raise @@ Consistency_error (ctx ^ ":\n" ^ err)

  let same_result a b = assert (a = b); a
  let same_result' msg a b = if (a <> b) then consistency_error msg; a

  let consistency_chk (h, dbg) =
    let h_list = List.sort (fun (k1, _) (k2, _) -> O.compare k1 k2) (Hamt.fold (fun k v xs -> (k, v) :: xs) h [])
    and dbg_list: (key * 'v) list = R.to_seq dbg |> Seq.fold_left (Fun.flip List.cons) [] |> List.rev
    and print_keys kvs = List.map fst kvs |> List.map P.pp |> List.fold_left (fun a b -> a ^ ", " ^ b) ""
    in ignore @@
    add_ctx (Printf.sprintf "hamt: %s" @@ print_keys h_list) @@
    lazy (add_ctx (Printf.sprintf "dbg: %s" @@ print_keys dbg_list) @@
    lazy (add_ctx (Printf.sprintf "hamt structure: %s" @@ Hamt.dbg P.pp h) @@
    lazy (same_result' "the maps aren't consistent" h_list dbg_list)));
    (h, dbg)

  let consistency_chk' msg x = add_ctx msg @@ lazy (consistency_chk x)

  let empty = Hamt.empty, R.empty
  let add k v (h, dbg) = consistency_chk' ("add " ^ P.pp k) (Hamt.add k v h, R.add k v dbg)
  let remove k (h, dbg) = consistency_chk' ("remove " ^ P.pp k ^ " hash = " ^ Printf.sprintf "%x" (H.hash k)) (Hamt.remove k h, R.remove k dbg)
  let find k (h, dbg) = same_result' ("find " ^ P.pp k) (Hamt.find k h) (R.find k dbg)
  let mem k (h, dbg) = same_result' ("mem " ^ P.pp k) (Hamt.mem k h) (R.mem k dbg)
  let update k f (h, dbg) = consistency_chk' ("update " ^ P.pp k) (Hamt.update k f h, R.update k f dbg)

  let fold f (h, dbg) acc = (Hamt.fold f h acc) (* R.fold f dbg acc *)
  
  let for_all (p : key -> 'v -> bool) (m : 'v t) : bool = fold ((fun k v rest -> rest && p k v) : 'k -> 'v -> bool -> bool) m true

  (* this is a bad (O(n)) implementation, TODO: proper removal, then just fetch
     the first binding. *)
  let choose_opt m =
    let f k v = function
      | Some x -> Some x
      | None -> Some ((k, v))
    in
    add_ctx "choose_opt" @@ lazy (fold f m None)

  let choose m = Stdlib.Option.get @@ choose_opt m
  let is_empty (h, dbg) = same_result' "is empty?" (Hamt.is_empty h) (R.is_empty dbg)

  let union resolve (h1, dbg1) (h2, dbg2) = (Hamt.union resolve h1 h2, R.union resolve dbg1 dbg2)

  let dbg pp (h, _) = Hamt.dbg pp h
end
