open Syntax
open Utils.Error

module TyManager = struct
  module StaticTy = Map.Make (struct type t = ty let compare = compare end)

  type state = {
    counter : int;
    cache : string StaticTy.t;
  }

  let current_state = ref {
    counter = 0;
    cache = StaticTy.empty;
  }

  let clear () = 
    current_state := { counter = 0; cache = StaticTy.empty }

  let save () = !current_state

  let restore s = 
    current_state := s

  let register u =
    if not (StaticTy.mem u !current_state.cache) then
      let c = !current_state.counter + 1 in
      let name = Printf.sprintf "ty%d" c in
      current_state := {
        counter = c;
        cache = StaticTy.add u name !current_state.cache;
      }

  let find u = StaticTy.find u !current_state.cache

  let get_definitions () = StaticTy.bindings !current_state.cache
end

module RangeManager = struct
  module Range = Map.Make (struct type t = range let compare = compare end)

  type state = {
    counter : int;
    cache : int Range.t;
  }

  let current_state = ref {
    counter = -1;
    cache = Range.empty;
  }

  let clear () = 
    current_state := { counter = -1; cache = Range.empty }

  let save () = !current_state

  let restore s = 
    current_state := s

  let range_id r = 
    try
      Range.find r !current_state.cache
    with Not_found ->
      let c = !current_state.counter + 1 in
      current_state := {
        counter = c;
        cache = Range.add r c !current_state.cache;
      };
      c

  let get_definitions () = Range.bindings !current_state.cache
end

module CrcManager = struct
  module StaticCrc = Map.Make (struct type t = Cls.coercion let compare = compare end)
  module AtomInjCrc = Map.Make (struct type t = string let compare = compare end)
  module AtomProjCrc = Map.Make (struct type t = string let compare = compare end)

  type state = {
    counter : int;
    cache : string StaticCrc.t;
  }

  let current_state = ref {
    counter = 0;
    cache = StaticCrc.empty;
  }

  let current_inj = ref AtomInjCrc.empty
  let current_proj = ref AtomProjCrc.empty

  let clear () = 
    current_state := { counter = 0; cache = StaticCrc.empty };
    current_inj := AtomInjCrc.empty;
    current_proj := AtomProjCrc.empty

  let save () = !current_state, !current_inj, !current_proj

  let restore (cs, ci, cp) = 
    current_state := cs;
    current_inj := ci;
    current_proj := cp

  let register s =
    if not (StaticCrc.mem s !current_state.cache) then
      let c = !current_state.counter + 1 in
      let name = Printf.sprintf "crc%d" c in
      current_state := {
        counter = c;
        cache = StaticCrc.add s name !current_state.cache;
      }
  
  let mem s = StaticCrc.mem s !current_state.cache

  let find s = StaticCrc.find s !current_state.cache

  let get_definitions () = StaticCrc.bindings !current_state.cache

  let register_inj (str: string) (tag: tag) =
    if not (AtomInjCrc.mem str !current_inj) then
      current_inj := AtomInjCrc.add str tag !current_inj
  
  let mem_inj str = AtomInjCrc.mem str !current_inj

  let find_inj str = AtomInjCrc.find str !current_inj

  let register_proj (str: string) ((tag, rid, p): tag * int * polarity) =
    if not (AtomProjCrc.mem str !current_proj) then
      current_proj := AtomProjCrc.add str (tag, rid, p) !current_proj
  
  let mem_proj str = AtomProjCrc.mem str !current_proj

  let find_proj str = AtomProjCrc.find str !current_proj
end

let static_clear () = 
  TyManager.clear ();
  RangeManager.clear ();
  CrcManager.clear ()

let static_save () =
  TyManager.save (), RangeManager.save (), CrcManager.save ()

let static_restore (s1, s2, s3) =
  TyManager.restore s1;
  RangeManager.restore s2;
  CrcManager.restore s3
