(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ELF and Mach-O object (.o) file reader                                    *)
(* ========================================================================= *)

(*** get int from bs[a:a+n-1] (little-endian). Fail if the resulting
     integer is too large to fit in OCaml int type (63 bits) ***)
let get_int_le (bs:bytes) a n =
  if n > 8 then failwith "get_int_le: n too big" else
  if n = 8 && Char.code (Bytes.get bs 7) >= 128
  then failwith "get_int_le: does not fit in OCaml int (63 bits)" else
  let rec fn a n =
    if n = 0 then 0 else
    Char.code (Bytes.get bs a) lor (fn (a+1) (n-1) lsl 8)
  in fn a n;;

(*** load the whole file at path f ***)
let load_file (f:string): bytes =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  s;;

let rec get_list bs a n: char list =
  if n = 0 then [] else Bytes.get bs a :: get_list bs (a+1) (n-1);;

let get_int_list bs a n: int list = map Char.code (get_list bs a n);;

let get_string bs (a:int): string =
  let rec len a n = if Bytes.get bs a = '\x00' then n else len (a+1) (n+1) in
  Bytes.sub_string bs a (len a 0);;


let is_elf (file:bytes) = get_list file 0x0 4 = ['\x7f'; 'E'; 'L'; 'F'];;
let is_elf_file (filename:string) = is_elf (load_file filename);;

(* ELF data layouts and constants follow the System V Generic ABI:

   ELF header and class-dependent types:
     https://gabi.xinuos.com/elf/02-eheader.html
   Section headers and section types:
     https://gabi.xinuos.com/elf/03-sheader.html
   Symbol table entries:
     https://gabi.xinuos.com/elf/05-symtab.html
   REL and RELA relocation entries:
     https://gabi.xinuos.com/elf/06-reloc.html
*)
type elf_class =
  | Elf32
  | Elf64;;

type elf_symbol = {
  elf_symbol_name: string;
  elf_symbol_value: int;
  elf_symbol_size: int;
  elf_symbol_type: int;
  elf_symbol_section_index: int;
  elf_symbol_section_name: string
};;

type elf_relocation = {
  elf_relocation_type: int;
  elf_relocation_offset: int;
  elf_relocation_symbol: elf_symbol;
  elf_relocation_addend: int
};;

type elf_layout = {
  elf_layout_ident_class: int;
  elf_layout_header_shoff: int * int;
  elf_layout_header_shentsize: int;
  elf_layout_header_shnum: int;
  elf_layout_header_shstrndx: int;
  elf_layout_section_header_size: int;
  elf_layout_section_offset: int * int;
  elf_layout_section_size: int * int;
  elf_layout_section_link: int;
  elf_layout_section_entsize: int * int;
  elf_layout_symbol_entry_size: int;
  elf_layout_symbol_info: int;
  elf_layout_symbol_shndx: int;
  elf_layout_symbol_value: int * int;
  elf_layout_symbol_size: int * int;
  elf_layout_relocation_entry_size: int;
  elf_layout_read_relocation_offset: bytes -> int -> int;
  elf_layout_read_relocation_type: bytes -> int -> int;
  elf_layout_read_relocation_symbol: bytes -> int -> int;
  elf_layout_read_relocation_addend: bytes -> int -> int
};;

let elf32_layout:elf_layout = {
  elf_layout_ident_class = 1;
  elf_layout_header_shoff = 0x20,4;
  elf_layout_header_shentsize = 0x2e;
  elf_layout_header_shnum = 0x30;
  elf_layout_header_shstrndx = 0x32;
  elf_layout_section_header_size = 40;
  elf_layout_section_offset = 0x10,4;
  elf_layout_section_size = 0x14,4;
  elf_layout_section_link = 0x18;
  elf_layout_section_entsize = 0x24,4;
  elf_layout_symbol_entry_size = 16;
  elf_layout_symbol_info = 12;
  elf_layout_symbol_shndx = 14;
  elf_layout_symbol_value = 4,4;
  elf_layout_symbol_size = 8,4;
  elf_layout_relocation_entry_size = 12;
  elf_layout_read_relocation_offset = (fun file off -> get_int_le file off 4);
  elf_layout_read_relocation_type = (fun file off ->
    get_int_le file (off + 4) 4 land 0xff);
  elf_layout_read_relocation_symbol = (fun file off ->
    get_int_le file (off + 4) 4 lsr 8);
  elf_layout_read_relocation_addend = (fun file off ->
    let n = get_int_le file (off + 8) 4 in
    if n land 0x80000000 = 0 then n else n - 0x100000000)
};;

let elf64_layout:elf_layout = {
  elf_layout_ident_class = 2;
  elf_layout_header_shoff = 0x28,8;
  elf_layout_header_shentsize = 0x3a;
  elf_layout_header_shnum = 0x3c;
  elf_layout_header_shstrndx = 0x3e;
  elf_layout_section_header_size = 64;
  elf_layout_section_offset = 0x18,8;
  elf_layout_section_size = 0x20,8;
  elf_layout_section_link = 0x28;
  elf_layout_section_entsize = 0x38,8;
  elf_layout_symbol_entry_size = 24;
  elf_layout_symbol_info = 4;
  elf_layout_symbol_shndx = 6;
  elf_layout_symbol_value = 8,8;
  elf_layout_symbol_size = 16,8;
  elf_layout_relocation_entry_size = 24;
  elf_layout_read_relocation_offset = (fun file off -> get_int_le file off 8);
  elf_layout_read_relocation_type = (fun file off ->
    get_int_le file (off + 0x8) 4);
  elf_layout_read_relocation_symbol = (fun file off ->
    get_int_le file (off + 0xc) 4);
  elf_layout_read_relocation_addend = (fun file off ->
    get_int_le file (off + 0x10) 8)
};;

let get_elf_layout = function
  | Elf32 -> elf32_layout
  | Elf64 -> elf64_layout;;

(*** Read the class-independent parts of an ELF relocatable object. Only an
     exact .rela.text/SHT_RELA relocation section is returned; any SHT_REL
     section is rejected and other relocation sections are ignored. The raw
     records retain symbol values and section information so a backend can
     validate offsets and apply instruction-specific relocations without
     re-parsing ELF32 or ELF64 structures. ***)
let load_elf_raw (elf_class:elf_class) (arch:int) (file:bytes):
      bytes *
      (string * bytes) list *
      elf_relocation list =
  let layout = get_elf_layout elf_class in

  if not (is_elf file) then failwith "not an ELF file" else
  if get_int_list file 0x4 5 <>
       [layout.elf_layout_ident_class;1;1;0;0]
  then failwith "not a supported ELF filetype" else
  if get_int_le file 0x12 2 <> arch then
    failwith ("unexpected ELF architecture: " ^
      Printf.sprintf "%x" (get_int_le file 0x12 2)) else

  let shoff_offset,shoff_size = layout.elf_layout_header_shoff in
  let shoff = get_int_le file shoff_offset shoff_size
  and shentsize = get_int_le file layout.elf_layout_header_shentsize 2
  and shnum = get_int_le file layout.elf_layout_header_shnum 2
  and shstrndx = get_int_le file layout.elf_layout_header_shstrndx 2 in
  if shentsize < layout.elf_layout_section_header_size then
    failwith "ELF section header is too small" else
  let section_headers = Array.init shnum (fun i ->
    Bytes.sub file (shoff + i * shentsize) shentsize) in

  let section_offset sec_header =
    let off,len = layout.elf_layout_section_offset in
    get_int_le sec_header off len
  and section_len sec_header =
    let off,len = layout.elf_layout_section_size in
    get_int_le sec_header off len
  and section_type sec_header = get_int_le sec_header 0x4 4
  and section_link sec_header =
    get_int_le sec_header layout.elf_layout_section_link 4
  and section_entsize sec_header =
    let off,len = layout.elf_layout_section_entsize in
    get_int_le sec_header off len in

  let section_contents sec_header =
    Bytes.sub file (section_offset sec_header) (section_len sec_header) in
  if shstrndx = 0xffff then failwith "no section header string table" else
  if shstrndx >= Array.length section_headers then
    failwith "bad section header string table index" else
  let shstrtab = section_contents section_headers.(shstrndx) in
  let section_name sec_header =
    get_string shstrtab (get_int_le sec_header 0 4) in
  let section_name_at idx =
    if idx < Array.length section_headers
    then section_name section_headers.(idx)
    else "" in
  let find_section_index name ty =
    let rec find_index i =
      if i = Array.length section_headers then
        failwith ("missing ELF section: " ^ name) else
      let header = section_headers.(i) in
      if section_name header = name then
        if section_type header = ty then i
        else failwith "unexpected section type"
      else find_index (i + 1) in
    find_index 0 in
  let find_section name ty =
    section_headers.(find_section_index name ty) in

  Array.iter (fun header ->
    if section_type header = 9 (* SHT_REL *) then
      failwith "ELF SHT_REL relocations are not supported; use SHT_RELA")
    section_headers;

  let text = section_contents (find_section ".text" 1 (* SHT_PROGBITS *)) in
  let rodata_index = catch (find_section_index ".rodata") 1 in
  let symtab_index = catch (find_section_index ".symtab") 2 in
  let symtab_header = option_map (fun i -> section_headers.(i)) symtab_index in
  let symtab_contents = option_map section_contents symtab_header in
  let symtab_entry_size =
    match symtab_header with
    | None -> layout.elf_layout_symbol_entry_size
    | Some header ->
      let n = section_entsize header in
      if n = 0 then layout.elf_layout_symbol_entry_size
      else if n < layout.elf_layout_symbol_entry_size then
        failwith "ELF symbol entry is too small"
      else n in
  let symbol_string_table =
    match symtab_header with
    | None -> None
    | Some header ->
      let idx = section_link header in
      if idx >= Array.length section_headers then
        failwith "bad symbol string table index" else
      let strtab_header = section_headers.(idx) in
      if section_type strtab_header <> 3 then
        failwith "symbol table does not reference a string table" else
      Some (section_contents strtab_header) in
  let symbol_count =
    match symtab_contents with
    | None -> 0
    | Some symtab ->
      if Bytes.length symtab mod symtab_entry_size <> 0 then
        failwith "bad ELF symbol table size" else
      Bytes.length symtab / symtab_entry_size in
  let symbol symtab_idx =
    if symtab_idx < 0 || symbol_count <= symtab_idx then
      failwith "bad ELF symbol index" else
    let symtab = option_get symtab_contents in
    let base = symtab_idx * symtab_entry_size in
    let value_off,value_len = layout.elf_layout_symbol_value
    and size_off,size_len = layout.elf_layout_symbol_size in
    let name_index = get_int_le symtab base 4 in
    let section_index =
      get_int_le symtab (base + layout.elf_layout_symbol_shndx) 2 in
    {
      elf_symbol_name =
        (match symbol_string_table with
         | None -> ""
         | Some strings -> get_string strings name_index);
      elf_symbol_value = get_int_le symtab (base + value_off) value_len;
      elf_symbol_size = get_int_le symtab (base + size_off) size_len;
      elf_symbol_type =
        get_int_le symtab (base + layout.elf_layout_symbol_info) 1 land 0xf;
      elf_symbol_section_index = section_index;
      elf_symbol_section_name = section_name_at section_index
    } in

  let rodata =
    match rodata_index,symtab_contents with
    | Some idx,Some _ ->
      let contents = section_contents section_headers.(idx) in
      let entries = ref [] in
      for i = 0 to symbol_count - 1 do
        let sym = symbol i in
        if sym.elf_symbol_type = 1 &&
           sym.elf_symbol_section_index = idx
        then
          let data = Bytes.sub contents sym.elf_symbol_value
            sym.elf_symbol_size in
          entries := (sym.elf_symbol_name,data)::!entries
      done;
      !entries @ ["WHOLE_READONLY",contents]
    | _ -> [] in

  let relocations =
    match catch (find_section ".rela.text") 4 (* SHT_RELA *) with
    | None -> []
    | Some rel_sec ->
      let linked_symtab = section_link rel_sec in
      (match symtab_index with
       | Some idx when idx = linked_symtab -> ()
       | Some _ ->
         failwith "relocation section references another symbol table"
       | None -> failwith "relocation section has no symbol table");
      let entry_size =
        let n = section_entsize rel_sec in
        if n = 0 then layout.elf_layout_relocation_entry_size
        else if n < layout.elf_layout_relocation_entry_size then
          failwith "ELF relocation entry is too small"
        else n in
      let rel_size = section_len rel_sec in
      if rel_size mod entry_size <> 0 then
        failwith "bad ELF relocation section size" else
      let rel_pos = section_offset rel_sec in
      let rel_end = rel_pos + rel_size in
      let rec read_relocations off =
        if off = rel_end then [] else
        {
          elf_relocation_type =
            layout.elf_layout_read_relocation_type file off;
          elf_relocation_offset =
            layout.elf_layout_read_relocation_offset file off;
          elf_relocation_symbol =
            symbol (layout.elf_layout_read_relocation_symbol file off);
          elf_relocation_addend =
            layout.elf_layout_read_relocation_addend file off
        }::read_relocations (off + entry_size) in
      read_relocations rel_pos in

  text,rodata,relocations;;

let load_elf_with_class elf_class arch reloc_type file =
  let text,rodata,relocations = load_elf_raw elf_class arch file in
  text,rodata,
  map (fun relocation ->
    let symbol = relocation.elf_relocation_symbol in
    reloc_type relocation.elf_relocation_type,
    (relocation.elf_relocation_offset,
     (if symbol.elf_symbol_type = 3 &&
         symbol.elf_symbol_section_name = ".rodata"
      then "WHOLE_READONLY"
      else symbol.elf_symbol_name),
     relocation.elf_relocation_addend))
    relocations;;

(*** Compatibility entry point for the existing AArch64 and x86-64
     backends. ***)
let load_elf arch reloc_type file =
  load_elf_with_class Elf64 arch reloc_type file;;

let load_elf32 arch reloc_type file =
  load_elf_with_class Elf32 arch reloc_type file;;

let load_elf64_raw arch file = load_elf_raw Elf64 arch file;;
let load_elf32_raw arch file = load_elf_raw Elf32 arch file;;

let load_elf_code arch file =
  let code,_,_ = load_elf arch
    (fun _ -> failwith "ELF contains relocations") file in
  code;;

let load_elf32_code arch file =
  let code,_,_ = load_elf32 arch
    (fun _ -> failwith "ELF contains relocations") file in
  code;;


(*** load_macho reads an object file, and returns the "__text" section bytes
    Reference: OS X ABI Mach-O File Format Reference
***)

let is_macho (file:bytes) =
  get_list file 0x0 4 = ['\207'; '\250'; '\237'; '\254'];;

let load_macho (cputype:int) (reloc_type:int -> 'a) (file:bytes):
    bytes * (* __text *)
    (string * bytes) list (* read-only data list *) *
    ('a * (int * string * int)) list (* relocation info *) =

  (* The magic number (64-bit). *)
  if not (is_macho file) then failwith "not a Mach-O file" else

  (* CPU type. 0x00000007 for x86, 0x0000000C for ARM. 0x01000000 bit
     set if 64-bit *)
  if get_int_le file 0x4 4 <> cputype then
    failwith "unexpected CPU type" else

  (* Get the Mach-O header. It is 32 bytes. *)
  (* Throw away CPU subtype and flags *)
  let num_load_commands = get_int_le file 16 4 and
      size_load_commands = get_int_le file 20 4 and
      filetype = get_int_le file 12 4 in
  if filetype <> 0x00000001 then failwith "Not a relocatable object file" else

  (* Now, read the following load commands *)
  let curr_file_offset = ref 0x20 in
  let sections = ref [] in (* a list of (section name, begin ofs, len) *)
  (* a list of struct nlist_64:
     (symbol name(string), n_type, n_sect, n_desc) *)
  let raw_symbols = ref [] in
  (* a list of struct relocation_info:
     (section idx, r_address, r_data, r_symbolnum, r_pcrel, r_length, r_extern, r_type) list. *)
  let raw_reloc_entries = ref [] in

  for i = 0 to num_load_commands - 1 do
    let cmd_type = get_int_le file !curr_file_offset 4 and
        cmd_size = get_int_le file (4 + !curr_file_offset) 4 in
    let next_file_offset = cmd_size + !curr_file_offset in

    (begin match cmd_type with
    | 0x00000019 -> begin (* Segment load (64 bit) *)
      (* Command name: LC_SEGMENT_64
         C struct: segment_command_64 *)

      (* Read the following struct section_64[]. *)
      let num_sections = get_int_le file (64 + !curr_file_offset) 4 in
      (* each section info consumes 80 bytes *)

      for j = 0 to num_sections - 1 do
        let ofs = 72(*size of load command *) + 80(*size of section info*) * j +
                  !curr_file_offset in
        let section_name = get_string file ofs in
        let file_offset = get_int_le file (48 + ofs) 4 in
        let section_size = get_int_le file (40 + ofs) 8 in
        sections := !sections @ [(section_name,file_offset,section_size)];

        (* Read struct relocation_info[]. *)
        (* file offset and count of relocation entries *)
        let reloc_ofs = get_int_le file (56 + ofs) 4 in
        let num_reloc_entries = get_int_le file (60 + ofs) 4 in
        for k = 0 to num_reloc_entries - 1 do
          let ofs = reloc_ofs + k * 8 in
          let r_address = get_int_le file (ofs) 4 in
          let r_data = get_int_le file (4 + ofs) 4 in
          let r_symbolnum = r_data land 0xFFFFFF in
          let r_pcrel = (r_data lsr 24) land 1 in
          let r_length = (r_data lsr 25) land 2 in
          let r_extern = (r_data lsr 27) land 1 in
          let r_type = (r_data lsr 28) in

          raw_reloc_entries := !raw_reloc_entries @
              [length !sections - 1, r_address, r_data, r_symbolnum, r_pcrel, r_length, r_extern, r_type]
        done
      done
      end
    | 0x00000032 -> begin (* Minimum OS version *)
      end
    | 0x00000002 -> begin (* __LINKEDIT Symbol table *)
      (* Command name: LC_SYMTAB
         C struct: symtab_command *)
      let nlist_ofs = get_int_le file (8 + !curr_file_offset) 4 in
      let num_symbols = get_int_le file (12 + !curr_file_offset) 4 in
      let string_table_ofs = get_int_le file (16 + !curr_file_offset) 4 in
      let string_table_sz = get_int_le file (20 + !curr_file_offset) 4 in

      (* Iterate each symbol table entry *)
      for j = 0 to num_symbols - 1 do
        (* struct nlist_64 *)
        let nlist_j = nlist_ofs + 16 * j in
        let strtable_idx = get_int_le file nlist_j 4 in
        let symbol_name = get_string file (string_table_ofs + strtable_idx) in
        let n_type = get_int_le file (4 + nlist_j) 1 in
        let n_sect = get_int_le file (5 + nlist_j) 1 in
        let n_desc = get_int_le file (6 + nlist_j) 2 in
        let n_value = get_int_le file (8 + nlist_j) 8 in

        raw_symbols := !raw_symbols @ [symbol_name, n_type, n_sect, n_desc, n_value]
      done
      end
    | 0x0000000b -> begin (* __LINKEDIT Symbol table information *)
      end
    | _ -> failwith ("Unknown load command: " ^ (string_of_int cmd_type) ^
            " (file byte offset: " ^ (string_of_int !curr_file_offset) ^ ")")
    end;
    curr_file_offset := next_file_offset)
  done;

  (* Get the readonly symbols from raw_symbols. *)
  let const_symbols = ref [] (* symbol name, byte offset *) in
  List.iter (fun symbol_name, n_type, n_sect, n_desc, n_value ->
    if n_type = 0xe (* N_SECT: The symbol is defined in a section at n_sect *) &&
      n_sect != 0 && (n_sect - 1) < List.length !sections &&
      (let secname,_,_ = List.nth !sections (n_sect - 1) in secname = "__const") &&
      (* Some symbols starting with "ltmp" are auto-generated. They are ignored by
        tools like:
        https://github.com/microsoft/llvm-mctoll/blob/master/MachODump.cpp#L228 *)
      not (starts_with "ltmp" symbol_name)
    then begin
      const_symbols := !const_symbols @ [(symbol_name, n_value(*byte offset *))]
    end) !raw_symbols;

  (* Sort the readonly symbols by their addresses.
     This is to 'infer' the sizes of each symbol. Mach-O symbol table does not
     have symbol sizes. *)
  const_symbols := sort (fun (_,addr1) (_,addr2) -> addr1 < addr2)
      !const_symbols;

  (* Now get the final results *)
  (* Helper functions *)
  let find_section (name:string): int * bytes =
    let res = find (fun section_name,_,_ -> section_name = name) !sections in
    match res with
    | _,beginofs,len -> (beginofs,Bytes.sub file beginofs len)
    | _ -> failwith ("Could not find a unique \"" ^ name ^ "\" section") in
  let rec extract_bytes (start_ofs:int) (end_ofs: int option) sections: bytes =
    match sections with
    | [] -> failwith "no available section"
    | s::sections' ->
      let symname,secofs,seclen = s in
      if start_ofs < seclen then
        let symbol_len = if end_ofs <> None
          then (option_get end_ofs - start_ofs)
          else seclen - start_ofs in
        Bytes.sub file (secofs + start_ofs) symbol_len
      else
        let end_ofs = option_map (fun x -> x - seclen) end_ofs in
        extract_bytes (start_ofs - seclen) end_ofs sections' in

  (* 1. The __text section data *)
  snd (find_section "__text"),

  (* 2. The readonly constants for each symbol, followed by "WHOLE_READONLY" and
        its whole byte contents *)
  (let consts = if length !const_symbols = 0 then [] else begin
    (* collect (symbol name, bytes) list *)
    let res = ref [] in
    for j = 0 to (length !const_symbols - 1) do
      let sname,ofs = List.nth !const_symbols j in
      let ofs_end = if j = length !const_symbols - 1 then None
        else Some (snd (List.nth !const_symbols (j+1))) in
      res := !res @ [sname, extract_bytes ofs ofs_end !sections]
    done;
    !res end in
    consts @ (match catch find_section "__const" with
    | Some (_, b) -> ["WHOLE_READONLY", b]
    | None -> [])),

  (* 3. Relocation entries *)
  (let res = ref [] in
    List.iter (fun section_idx, r_address, r_data, r_symbolnum, r_pcrel, r_length, r_extern, r_type ->
      if r_type = 10 then
        (* ARM64_RELOC_ADDEND "Must be followed by ARM64_RELOC_PAGE21 or
           ARM64_RELOC_PAGEOFF12" (per llvm/include/llvm/BinaryFormat/MachO.h)*)
        let relty,(addr,symbolname,addend) = last !res in
        if addend <> 0 then
          failwith "ARM64_RELOC_ADDEND but previous addend nonzero!"
        else
          let new_addend = r_symbolnum in
          res := (butlast !res) @ [relty,(addr,symbolname,new_addend)]

      else if r_type = 0 || r_type = 1 then
        (* 0: ARM64_RELOC_UNSIGNED.
           1: ARM64_RELOC_SUBTRACTOR.
           These relocation entry types are used by CFI. *)
        ()

      else
        let symbolname,_,_,_,_ = List.nth !raw_symbols r_symbolnum in
        res := !res @ [reloc_type r_type,
          (r_address, symbolname,
           0 (* corresponds to "addend" in ELF relocation entry. This will be
                filled by the following ARM64_RELOC_ADDEND if exists. *))]
      )
      (* order of raw_reloc_entries matters because ARM64_RELOC_ADDEND
         depends on it. *)
      (rev !raw_reloc_entries);
    (* sort the result *)
    sort (fun (_,(i1,_,_)) (_,(i2,_,_)) -> i1 < i2) !res
  );;

let load_macho_code arch file =
  let code,_,_ = load_macho arch
    (fun _ -> failwith "MachO contains relocations") file in
  code;;

(*** TODO: rename these to "load_obj_contents_*" or something else
     because they can also recognize the Mach-O format ***)
let load_elf_contents_x86 path =
  let file = load_file path in
  if is_macho file then load_macho_code 0x01000007 file (* x86, 64-bit *)
  else if is_elf file then load_elf_code 62 file (* x86-64 *)
  else failwith "Neither ELF nor Mach-O";;

let load_elf_contents_arm path =
  let file = load_file path in
  if is_macho file then load_macho_code 0x0100000C file (* ARM, 64-bit *)
  else if is_elf file then load_elf_code 183 file (* ARM AARCH64 *)
  else failwith "Neither ELF nor Mach-O";;


(* s2n-bignum data structure for representing relocations.
  The full list can be found from
  https://github.com/lattera/glibc/blob/master/elf/elf.h#L2731.

  For Arm, their meanings can be found from 5.7.3. Relocation types in
  https://github.com/ARM-software/abi-aa/blob/main/aaelf64/aaelf64.rst#5733relocation-operations.

  For x86, their meanings can be found from
  https://refspecs.linuxbase.org/elf/x86_64-abi-0.99.pdf.

  The naming of these constructors follow those of ELF, but they are
  reused for the Mach-O format.
*)

type x86_reloc =
  | X86_64_pc32;;

type arm_reloc =
  | Arm_condbr19 (* conditional branches *)
  | Arm_call26 (* BL *)
  | Arm_adr_prel_lo21 (* ADR *)
  | Arm_adr_prel_pg_hi21 (* ADRP; this is ARM64_RELOC_PAGE21 in Mach-O *)
  | Arm_add_abs_lo12_nc (* ADD; this is ARM64_RELOC_PAGEOFF12 in Mach-O  *);;
(* Note: there is no ARM64_RELOC_ADDEND in this list! It is immediately
   processed by load_macho. *)

let load_elf_x86 (bs:bytes) =
  if is_macho bs then
      load_macho 0x01000007 (function
      (* See the full list from:
        https://github.com/llvm/llvm-project/blob/main/llvm/include/llvm/BinaryFormat/MachO.h *)
      | 1 (* X86_64_RELOC_SIGNED *) -> X86_64_pc32
      | n -> failwith (sprintf "unexpected relocation type: %d" n))
      bs
  else
    load_elf (62 (* x86-64 *))
      (function
      (* See the full list from:
         https://refspecs.linuxbase.org/elf/x86_64-abi-0.99.pdf *)
      | 2 (* R_X86_64_PC32 *) -> X86_64_pc32
      | n -> failwith (sprintf "unexpected relocation type: %d" n))
      bs;;

let load_elf_arm (bs:bytes):
    bytes(*.text*) *
    (string * bytes) list * (arm_reloc * (int * string * int)) list =
  if is_macho bs then
    load_macho 0x0100000C (function
      (* See the full list from:
         https://github.com/llvm/llvm-project/blob/main/llvm/include/llvm/BinaryFormat/MachO.h *)
      | 3 (* ARM64_RELOC_PAGE21 *) -> Arm_adr_prel_pg_hi21
      | 4 (* ARM64_RELOC_PAGEOFF12 *) -> Arm_add_abs_lo12_nc
      | n -> failwith (sprintf "unexpected relocation type: %d" n))
      bs
  else
    load_elf (183 (* ARM AARCH64 *))
      (function
      (* See the full list from:
          https://github.com/lattera/glibc/blob/master/elf/elf.h#L2731 *)
      | 274 (* R_AARCH64_ADR_PREL_LO21 *) -> Arm_adr_prel_lo21
      | 275 (* R_AARCH64_ADR_PREL_PG_HI21  *) -> Arm_adr_prel_pg_hi21
      | 277 (* R_AARCH64_ADD_ABS_LO12_NC  *) -> Arm_add_abs_lo12_nc
      | 280 (* R_AARCH64_CONDBR19 *) -> Arm_condbr19
      | 283 (* R_AARCH64_CALL26 *) -> Arm_call26
      | n -> failwith (sprintf "unexpected relocation type: %d" n))
      bs;;

let term_of_list_int,app_term_of_int_fun,term_of_int_fun =
  let word = `word:num->byte`
  and nil = `NIL:byte list`
  and cons = `CONS:byte->byte list->byte list` in
  let cons_word n e =
    mk_comb (mk_comb (cons, mk_comb (word, mk_numeral (num n))), e) in
  let app_term_of_int_fun f start end_ =
    let rec go n e =
      if n = start then e else
      let n' = n - 1 in
      go n' (cons_word (f n') e) in
    go end_ in
  C (itlist cons_word) nil, app_term_of_int_fun,
  fun f start end_ -> app_term_of_int_fun f start end_ nil;;

(* # term_of_int_fun (fun i -> i * 2) 10 20;;

  - : term =
  `[word 20; word 22; word 24; word 26; word 28; word 30; word 32; word 34;
    word 36; word 38]`

  # app_term_of_int_fun (fun x -> x+10) 1 5 `[word 0; word 1]:byte list`;;

  - : term = `[word 11; word 12; word 13; word 14; word 0; word 1]`
*)

let term_of_bytes bs =
  term_of_int_fun (Char.code o Bytes.get bs) 0 (Bytes.length bs);;
let term_of_array bs =
  term_of_int_fun (Array.get bs) 0 (Array.length bs);;
let array_of_bytes bs =
  Array.init (Bytes.length bs) (Char.code o Bytes.get bs);;

let define_word_list name tm =
  try new_definition (mk_eq (mk_var (name,`:byte list`),tm))
  with Failure _ ->
    new_definition (mk_eq (mk_mconst (name,`:byte list`),tm));;

(* term_of_relocs returns:
  (a list of HOL Light variables that are used to represent addresses of
   relocatable symbols,
   a symbolic byte list in term type)
*)
let term_of_relocs reloc_fn (bstext,constants,rels) =
  let rec go = function
  | [], start ->
    [], term_of_int_fun (Char.code o Bytes.get bstext) start (Bytes.length bstext)
  | (ty,(off,sym,(add:int)))::ls, start ->
    let sym = mk_var(sym,`:num`) in
    let n, app = reloc_fn(bstext,ty,off,sym,add) in
    let args, e = go (ls, off+n) in
    insert sym args,
    app_term_of_int_fun (Char.code o Bytes.get bstext) start off (app e) in
  let args, e = go (rels, 0) in
  `pc:num` :: args, e;;
