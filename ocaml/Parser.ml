let (|>) x f = f x

(******************************************************************************)
module type AST = sig
  type tree_node

  type 'a tree

  val new_result : int -> int -> tree_node tree -> tree_node

  val add_result : tree_node -> tree_node tree -> unit
end

module type RHS = sig
  type token
  type non_terminal

  type tree_node

  type 'a t

  val return  : 'a -> 'a t
  val (>>=)   : 'a t -> ('a -> 'b t) -> 'b t

  val failure : 'a t
  val (|||)   : 'a t -> 'a t -> 'a t

  val token   : token t
  val call    : non_terminal -> tree_node t
end

module type Grammar = sig
  type nt

  type token

  type 'a tree

  module Productions
    (RHS : RHS
     with type token = token
     and  type non_terminal = nt) :
  sig
    val of_nonterminal : nt -> RHS.tree_node tree RHS.t
  end
end

module ExpressionGrammar = struct
  type nt = S | E

  type token = char

  type 'a tree =
    | Doc  of 'a
    | Var
    | Plus of 'a * 'a

  module Productions
    (RHS : RHS with type token        = token
               and  type non_terminal = nt)
    =
  struct
    open RHS
    let of_nonterminal = function
      | S -> call E >>= fun e -> return (Doc e)
      | E ->
        (token >>= fun c ->
         if c = 'x' then
           return Var
         else
           failure)
        |||
        (call E >>= fun e1 ->
         call E >>= fun e2 ->
         return (Plus (e1, e2)))
  end
end

module MakeSPPF (T : sig type 'a tree end)
  : sig
    type tree_node = Node of tree_node T.tree list ref

    include (AST with type tree_node := tree_node
                 and  type 'a tree   = 'a T.tree)
  end
  =
struct
  type tree_node = Node of tree_node T.tree list ref

  type 'a tree = 'a T.tree

  let new_result i j t = Node (ref [t])
  let add_result (Node node) t = node := t :: !node
end

module MakeBasic (T : sig type 'a tree end) : sig
  type tree_node =
      { start_pos : int
      ; end_pos   : int
      ; value     : tree_node T.tree
      }

  include (AST with type tree_node := tree_node
               and  type 'a tree   = 'a T.tree)
end
  =
struct
  type tree_node =
      { start_pos : int
      ; end_pos   : int
      ; value     : tree_node T.tree
      }

  type 'a tree = 'a T.tree

  let new_result i j t = {start_pos = i; end_pos = j; value = t}
  let add_result t _ =
    failwith (Printf.sprintf "ambiguity detected between %d and %d" t.start_pos t.end_pos)
end

module type ImperativeMap = sig
  type 'a t
  type key
  val create : unit -> 'a t
  val lookup : key -> 'a t -> 'a option
  val insert : key -> 'a -> 'a t -> unit
end

module type ImperativeSet = sig
  type t
  type elt
  val create : unit -> t
  val mem    : elt -> t -> bool
  val add    : elt -> t -> unit
end

module Parser
  (G   : Grammar with type token = char)
  (AST : AST with type 'a tree = 'a G.tree)
  :
sig
  val parse : G.nt -> string -> AST.tree_node option
end
  =
struct
  module RHS = struct
    type token = G.token
    type non_terminal = G.nt
    type tree_node = AST.tree_node

    type 'a t =
      | Return      of 'a
      | Failure
      | Choice      of 'a t * 'a t
      | Token       of (token -> 'a t)
      | NonTerminal of non_terminal * (tree_node -> 'a t)

    let return x = Return x
    let rec (>>=) x f = match x with
      | Return a            -> f a
      | Failure             -> Failure
      | Choice (rhs1, rhs2) -> Choice (rhs1 >>= f, rhs2 >>= f)
      | Token k             -> Token (fun c -> k c >>= f)
      | NonTerminal (nt, k) -> NonTerminal (nt, fun v -> k v >>= f)

    let failure = Failure
    let (|||) rhs1 rhs2 = Choice (rhs1, rhs2)
    let token = Token return
    let call nt = NonTerminal (nt, return)
  end

  module Productions = G.Productions (RHS)

  (* Graph structured stacks *)
  type stack_node =
      {         position : int
      ;         nt       : G.nt
      ; mutable callers  : witem list
      }

  and witem =
      { wrhs            : (AST.tree_node -> AST.tree_node AST.tree RHS.t)
      ; wreturn_address : stack_node
      }

  let new_stack_node j nt =
    { position = j; nt; callers = [] }

  (* Items *)
  type item =
      { rhs            : AST.tree_node AST.tree RHS.t
      ; return_address : stack_node
      }

  (* Stack nodes are easy to compare for equality, but rhs's
     aren't. Need a way of reifying the contained state. Part of the
     state is the tree that is being built. Zippers are the obvious
     data structure that is needed to represent half-built
     tree-levels. *)

  let item_of_waiting v {wrhs;wreturn_address} =
    { rhs            = wrhs v
    ; return_address = wreturn_address
    }

  (* FIXME: take these data structures as functor parameters *)
  module PosNTMap =
    Map.Make (struct type t = int * G.nt
                     let compare = Pervasives.compare end)

  module NTMap =
    Map.Make (struct type t = G.nt
                     let compare = Pervasives.compare end)

  module NTSet =
    Set.Make (struct type t = G.nt
                     let compare = Pervasives.compare end)

  (******************************************************************************)
  let execute_items token j items =
    let continuing = ref [] in
    let known      = ref PosNTMap.empty in
    let called     = ref NTSet.empty in
    let waiting    = ref NTMap.empty in

    let is_known i nt =
      try Some (PosNTMap.find (i,nt) !known) with Not_found -> None
    in

    let add_waiting_item nt witem =
      match try Some (NTMap.find nt !waiting) with Not_found -> None with
        | None ->
          let stack_node = new_stack_node j nt in
          stack_node.callers <- witem :: stack_node.callers;
          waiting := NTMap.add nt stack_node !waiting;
          stack_node
        | Some stack_node ->
          stack_node.callers <- witem :: stack_node.callers;
          stack_node
    in

    let rec execute {rhs;return_address} = match rhs with
      | RHS.Return a ->
        let {position=i; nt} = return_address in
        (match is_known i nt with
          | None ->
            let v = AST.new_result i j a in
            known := PosNTMap.add (i,nt) v !known;
            return_address.callers |> List.iter begin fun witem ->
              execute (item_of_waiting v witem)
            end
          | Some v ->
            AST.add_result v a)

      | RHS.Failure -> 
        ()

      | RHS.Choice (rhs1, rhs2) ->
        execute {rhs=rhs1; return_address};
        execute {rhs=rhs2; return_address}

      | RHS.Token k ->
        (match token with
          | None   -> ()
          | Some t ->
            continuing := {rhs = k t; return_address} :: !continuing)

      | RHS.NonTerminal (nt, k) ->
        let witem = {wrhs=k; wreturn_address=return_address} in
        let stack_node = add_waiting_item nt witem in
        (match is_known j nt with
          | Some v ->
            execute {rhs = k v; return_address}
          | None when NTSet.mem nt !called ->
            ()
          | None ->
            called := NTSet.add nt !called;
            let item =
              { rhs            = Productions.of_nonterminal nt
              ; return_address = stack_node
              }
            in
            execute item)
    in
    List.iter execute items;
    (!continuing, !known)

  let parse nt string =
    let rec loop i items =
      if i = String.length string then
        let _, complete = execute_items None i items in
        try Some (PosNTMap.find (0,nt) complete) with Not_found -> None
      else
        let tok = string.[i] in
        let new_items, _ = execute_items (Some tok) i items in
        loop (i+1) new_items
    in
    let item =
      { rhs            = Productions.of_nonterminal nt
      ; return_address = new_stack_node 0 nt
      }
    in
    loop 0 [item]
end

module P_SPPF =
  Parser (ExpressionGrammar) (MakeSPPF (ExpressionGrammar))
