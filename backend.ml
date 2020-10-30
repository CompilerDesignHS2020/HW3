(* ll ir compilation -------------------------------------------------------- *)

open Ll
open X86

(* Overview ----------------------------------------------------------------- *)

(* We suggest that you spend some time understanding this entire file and
   how it fits with the compiler pipeline before making changes.  The suggested
   plan for implementing the compiler is provided on the project web page.
*)


(* helpers ------------------------------------------------------------------ *)

let last_elem_of (l: 'a list)=
  print_endline @@ Int.to_string ((List.length l)-1);
  List.nth l ((List.length l)-1)

(* Map LL comparison operations to X86 condition codes *)
let compile_cnd = function
  | Ll.Eq  -> X86.Eq
  | Ll.Ne  -> X86.Neq
  | Ll.Slt -> X86.Lt
  | Ll.Sle -> X86.Le
  | Ll.Sgt -> X86.Gt
  | Ll.Sge -> X86.Ge



(* locals and layout -------------------------------------------------------- *)

(* One key problem in compiling the LLVM IR is how to map its local
   identifiers to X86 abstractions.  For the best performance, one
   would want to use an X86 register for each LLVM %uid.  However,
   since there are an unlimited number of %uids and only 16 registers,
   doing so effectively is quite difficult.  We will see later in the
   course how _register allocation_ algorithms can do a good job at
   this.

   A simpler, but less performant, implementation is to map each %uid
   in the LLVM source to a _stack slot_ (i.e. a region of memory in
   the stack).  Since LLVMlite, unlike real LLVM, permits %uid locals
   to store only 64-bit data, each stack slot is an 8-byte value.

   [ NOTE: For compiling LLVMlite, even i1 data values should be
   represented as a 8-byte quad. This greatly simplifies code
   generation. ]

   We call the datastructure that maps each %uid to its stack slot a
   'stack layout'.  A stack layout maps a uid to an X86 operand for
   accessing its contents.  For this compilation strategy, the operand
   is always an offset from %rbp (in bytes) that represents a storage slot in
   the stack.
*)

type layout = (uid * X86.operand) list

(* A context contains the global type declarations (needed for getelementptr
   calculations) and a stack layout. *)
type ctxt = { tdecls : (tid * ty) list
            ; layout : layout
            }

(* useful for looking up items in tdecls or layouts *)
let lookup m x = List.assoc x m


(* compiling operands  ------------------------------------------------------ *)

(* LLVM IR instructions support several kinds of operands.

   LL local %uids live in stack slots, whereas global ids live at
   global addresses that must be computed from a label.  Constants are
   immediately available, and the operand Null is the 64-bit 0 value.

     NOTE: two important facts about global identifiers:

     (1) You should use (Platform.mangle gid) to obtain a string
     suitable for naming a global label on your platform (OS X expects
     "_main" while linux expects "main").

     (2) 64-bit assembly labels are not allowed as immediate operands.
     That is, the X86 code: movq _gid %rax which looks like it should
     put the address denoted by _gid into %rax is not allowed.
     Instead, you need to compute an %rip-relative address using the
     leaq instruction:   leaq _gid(%rip).

   One strategy for compiling instruction operands is to use a
   designated register (or registers) for holding the values being
   manipulated by the LLVM IR instruction. You might find it useful to
   implement the following helper function, whose job is to generate
   the X86 instruction that moves an LLVM operand into a designated
   destination (usually a register).
*)
let compile_operand (ctxt:ctxt) (dest:X86.operand) : Ll.operand -> ins =
  function ll_op -> 
  match ll_op with
    | Null -> (Movq, [Imm(Lit(0L)); dest])
    | Const(c) -> (Movq, [Imm(Lit(c)); dest])
    | Gid(g) -> (Leaq, [Ind1(Lbl(g)); dest])
    | Id(l) -> (Movq, [lookup ctxt.layout l;dest])

(* saves content of src to specifed uid *)
let compile_result (ctxt:ctxt) (src:X86.operand) : uid -> ins =
  function uid -> 
  (Movq, [src; lookup ctxt.layout uid])


(* [size_ty] maps an LLVMlite type to a size in bytes.
    (needed for getelementptr)

   - the size of a struct is the sum of the sizes of each component
   - the size of an array of t's with n elements is n * the size of t
   - all pointers, I1, and I64 are 8 bytes
   - the size of a named type is the size of its definition

   - Void, i8, and functions have undefined sizes according to LLVMlite.
     Your function should simply return 0 in those cases
*)
let rec size_ty (tdecls:(tid * ty) list) (t:Ll.ty) : int =
match t with
  | Void -> 0
  | I1 -> 8
  | I8 -> 0
  | I64 -> 8
  | Ptr(ty) -> 8
  | Struct(h::tl) -> (size_ty tdecls h) + (size_ty tdecls (Struct(tl)))
  | Array(size, ty) -> size * (size_ty tdecls ty)
  | Fun(args, ret) -> 0
  | Namedt(tid) -> size_ty tdecls (lookup tdecls tid)
  | _ -> 0

(* compiling getelementptr (gep)  ------------------------------------------- *)

(* The getelementptr instruction computes an address by indexing into
   a datastructure, following a path of offsets.  It computes the
   address based on the size of the data, which is dictated by the
   data's type.

   To compile getelementptr, you must generate x86 code that performs
   the appropriate arithmetic calculations.
*)


(* Generates code that computes a pointer value.

   1. op must be of pointer type: t*

   2. the value of op is the base address of the calculation

   3. the first index in the path is treated as the index into an array
     of elements of type t located at the base address

   4. subsequent indices are interpreted according to the type t:

     - if t is a struct, the index must be a constant n and it
       picks out the n'th element of the struct. [ NOTE: the offset
       within the struct of the n'th element is determined by the
       sizes of the types of the previous elements ]

     - if t is an array, the index can be any operand, and its
       value determines the offset within the array.

     - if t is any other type, the path is invalid

   5. if the index is valid, the remainder of the path is computed as
      in (4), but relative to the type f the sub-element picked out
      by the path so far
*)




let compile_gep (ctxt:ctxt) (op : Ll.ty * Ll.operand) (path: Ll.operand list) : ins list =

  let op_to_const op =
    match op with
      | Null -> 0
      | Const(c) -> Int64.to_int c
      | Gid(d) -> 0 (* Should raise an error *)
      | Id(uid) -> 0 (* Should raise an error *)
  in

  (* returns offset of struct item at index struc_ind *)
  let rec struct_offset act_ty_list struct_ind =
    begin match act_ty_list with
      | struct_h::struct_tl -> 
        if struct_ind = 0 then (0)
        (* calc size of current elem in struct + size remaining elems *) 
        else size_ty ctxt.tdecls struct_h + struct_offset struct_tl (struct_ind - 1)
      | [] -> 0
    end
  in

  (* returns struct item at index struc_ind *)
  let rec struct_elem_ty act_ty_list struct_ind =
    begin match act_ty_list with
      | struct_h::struct_tl -> 
        if struct_ind = 0 then struct_h
        else struct_elem_ty struct_tl (struct_ind - 1)
      | [] -> Void
    end
  in

  let rec calc_offset act_ty ind_list =   
      begin match ind_list with
        | act_path_ind::path_tl -> 

        (* Current type has subtype *)
        begin match act_ty with
          
          | Array(size, new_ty) -> 
          (calc_offset new_ty path_tl)@
          [compile_operand ctxt (Reg(Rdx)) act_path_ind]@
          [(Imulq, [Imm(Lit(Int64.of_int (size_ty ctxt.tdecls new_ty))); (Reg(Rdx))])]@
          [(Addq, [(Reg(Rdx));(Reg(Rax))])]
          | Struct(ty_list) -> 
          (* total size = size of previous struct elems t + size of act elem*)
          (calc_offset (struct_elem_ty ty_list (op_to_const act_path_ind) ) path_tl)@
          [(Movq, [Imm(Lit(Int64.of_int (struct_offset ty_list (op_to_const act_path_ind)))); (Reg(Rdx))])]@
          [(Addq, [(Reg(Rdx));(Reg(Rax))])]
          
          
          | Namedt(tid) -> calc_offset (lookup ctxt.tdecls tid) ind_list
          | _ -> [] (* should not happen *)
      end
      | [] -> 
      begin match act_ty with
        (* Current type has no subtype *)

        | Void | I1 | I8 | I64 -> [(Movq, [Imm(Lit(0L)); (Reg(Rax))])]
        | Ptr(ty) -> [(Movq, [Imm(Lit(0L)); (Reg(Rax))])]
        | Fun(arg_ty_list, ret_ty) -> [(Movq, [Imm(Lit(0L)); (Reg(Rax))])]
        | Namedt(tid) -> calc_offset (lookup ctxt.tdecls tid) ind_list

        | _ -> [] (* should not happen *)
      end
    end
  in 

  let (ty, base_addr_operand) = op in
  let offset_ins = calc_offset (Array(Int32.to_int Int32.max_int,ty)) path in
  offset_ins@[compile_operand ctxt (Reg(Rdx)) base_addr_operand]@[(Addq, [Reg(Rdx);Reg(Rax)])]

(* compiling call  ---------------------------------------------------------- *)

(* You will probably find it helpful to implement a helper function that
   generates code for the LLVM IR call instruction.

   The code you generate should follow the x64 System V AMD64 ABI
   calling conventions, which places the first six 64-bit (or smaller)
   values in registers and pushes the rest onto the stack.  Note that,
   since all LLVM IR operands are 64-bit values, the first six
   operands will always be placed in registers.  (See the notes about
   compiling fdecl below.)

   [ NOTE: It is the caller's responsibility to clean up arguments
   pushed onto the stack, so you must free the stack space after the
   call returns. ]

   [ NOTE: Don't forget to preserve caller-save registers (only if
   needed). ]
*)


(* compiling instructions  -------------------------------------------------- *)

(* The result of compiling a single LLVM instruction might be many x86
   instructions.  We have not determined the structure of this code
   for you. Some of the instructions require only a couple of assembly
   instructions, while others require more.  We have suggested that
   you need at least compile_operand, compile_call, and compile_gep
   helpers; you may introduce more as you see fit.

   Here are a few notes:

   - Icmp:  the Setb instruction may be of use.  Depending on how you
     compile Cbr, you may want to ensure that the value produced by
     Icmp is exactly 0 or 1.

   - Load & Store: these need to dereference the pointers. Const and
     Null operands aren't valid pointers.  Don't forget to
     Platform.mangle the global identifier.

   - Alloca: needs to return a pointer into the stack

   - Bitcast: does nothing interesting at the assembly level
*)

(* op1 is always loaded to rdx, op2 to rax *)
let compile_insn (ctxt:ctxt) ((uid:uid), (i:Ll.insn)) : X86.ins list =
  match i with
    (*compile arithmetic, bitshift and logical insns *)
    | Binop(operator, ty, op1, op2) -> 
      let x86_ins_dest = compile_operand ctxt (Reg(Rdx)) op1 in
      let x86_ins_src = 

      (*bitshift insns must use Reg rcx for amount *)
      begin match operator with
        | Shl | Lshr | Ashr -> compile_operand ctxt (Reg(Rcx)) op2
        | _ -> compile_operand ctxt (Reg(Rax)) op2
      end in
      let x86_ins_calc =
      begin match operator with
        | Add -> (Addq, [(Reg(Rax)); (Reg(Rdx))])
        | Sub -> (Subq, [(Reg(Rax)); (Reg(Rdx))])
        | Mul -> (Imulq, [(Reg(Rax)); (Reg(Rdx))])
        | Shl -> (Shlq, [(Reg(Rcx)); (Reg(Rdx))])
        | Lshr -> (Shrq, [(Reg(Rcx)); (Reg(Rdx))])
        | Ashr -> (Sarq, [(Reg(Rcx)); (Reg(Rdx))])
        | And -> (Andq, [(Reg(Rax)); (Reg(Rdx))])
        | Or -> (Orq, [(Reg(Rax)); (Reg(Rdx))])
        | Xor -> (Xorq, [(Reg(Rax)); (Reg(Rdx))])
      end
      in
      let x86_ins_store = compile_result ctxt (Reg(Rdx)) uid in
      [x86_ins_dest;x86_ins_src;x86_ins_calc;x86_ins_store]
      
      (*compile icmp insns *)
    | Icmp(cnd, ty, op1, op2) -> 
      let x86_ins_dest = compile_operand ctxt (Reg(Rdx)) op1 in
      let x86_ins_src = compile_operand ctxt (Reg(Rax)) op2 in
      let x86_insns_cmp =
      [(Cmpq, [(Reg(Rax)); (Reg(Rdx))]);
      (Set(compile_cnd cnd), [(Reg(Rdx))]) 
      ]
      in
      let x86_ins_store = compile_result ctxt (Reg(Rdx)) uid in
      [x86_ins_dest;x86_ins_src]@x86_insns_cmp@[x86_ins_store]

      (*compile alloca insns *)
    | Alloca(ty) ->  
      let x86_ins_alloc = (Subq, [Imm(Lit(Int64.of_int (size_ty ctxt.tdecls ty))); (Reg(Rsp))]) in
      let x86_ins_store = compile_result ctxt (Reg(Rsp)) uid in
      [x86_ins_alloc]@[x86_ins_store]

    (*x86 is untyped, so don't care types, just move ll_op to corresponding x86 reg / stack *)
    | Bitcast(ty1, op, ty2) -> 
    [compile_operand ctxt (Reg(Rax)) op]@[compile_result ctxt (Reg(Rax)) uid]

    (* load pointer in Rax, dereference Rax into Rdx, store Rdx at uid *)
    | Load(ty, op) -> 
      let x86_ins_src_ptr = compile_operand ctxt (Reg(Rax)) op in
      let x86_ins_src = (Movq, [Ind2(Rax);Reg(Rdx)]) in
      let x86_ins_load = compile_result ctxt (Reg(Rdx)) uid in
      [x86_ins_src_ptr;x86_ins_src;x86_ins_load]

    | Store(ty, op1, op2) ->
      let x86_ins_ptr = compile_operand ctxt (Reg(Rdx)) op2 in
      let x86_ins_src = compile_operand ctxt (Reg(Rax)) op1 in
      let x86_ins_store = (Movq, [Reg(Rax); Ind2(Rdx)]) in
      [x86_ins_ptr;x86_ins_src;x86_ins_store]

    | Call(ty, op, args) ->

      (* fill all arguments to reg / stack according System V ABI calling conventon *)
      let rec fill_args act_args =
      begin match act_args with
        | [] -> []
        | (ll_ty, ll_op)::tl ->  let ind = (List.length args - List.length act_args) in
          begin match (ind) with
          | 0 -> [compile_operand ctxt (Reg(Rdi)) ll_op]@(fill_args tl)
          | 1 -> [compile_operand ctxt (Reg(Rsi)) ll_op]@(fill_args tl)
          | 2 -> [compile_operand ctxt (Reg(Rdx)) ll_op]@(fill_args tl)
          | 3 -> [compile_operand ctxt (Reg(Rcx)) ll_op]@(fill_args tl)
          | 4 -> [compile_operand ctxt (Reg(R08)) ll_op]@(fill_args tl)
          | 5 -> [compile_operand ctxt (Reg(R09)) ll_op]@(fill_args tl)
          (*the sixth element is the first which is directly on the stack
          start filling in stack from adress of rsp - 2*int64
          *)
          | _ -> 
          let dest = Ind3(Lit(Int64.of_int ((-(ind-6)-3)*8)), Rsp) in
          [compile_operand ctxt (Reg(Rax)) ll_op; (Movq, [Reg(Rax); dest])]@(fill_args tl)
        end
      end
      in 
      let x86_ins_fill = fill_args args in

      (* compile ins for calling address in op*)
      let x86_ins_call = 
      [compile_operand ctxt (Reg(R10)) op]@
      [(Callq, [Reg(R10)])] in

      (* comile ins for store rax in uid*)
      let x86_ins_store_ret = [compile_result ctxt (Reg(Rax)) uid] in
      
      (*return all insns as ins list *)
      x86_ins_fill@x86_ins_call@x86_ins_store_ret

      | Gep(ty, op,) 

    | _ -> []



(* compiling terminators  --------------------------------------------------- *)

(* prefix the function name [fn] to a label to ensure that the X86 labels are 
   globally unique . *)
let mk_lbl (fn:string) (l:string) = fn ^ "." ^ l

(* Compile block terminators is not too difficult:

   - Ret should properly exit the function: freeing stack space,
     restoring the value of %rbp, and putting the return value (if
     any) in %rax.

   - Br should jump

   - Cbr branch should treat its operand as a boolean conditional

   [fn] - the name of the function containing this terminator
*)
let compile_terminator (fn:string) (ctxt:ctxt) (t:Ll.terminator) : ins list =
  begin match t with
    (* ret value in rax, reset rsp, reset rbp value (resp. pop rbp), last but not least: ret*)
    | Ret(ret_type, opt) -> 
      let rax_ins =  
        begin match opt with
          | None -> []
          | Some operand -> [compile_operand ctxt (Reg(Rax)) operand]
        end
      in
      rax_ins@
      (*[(Addq, [Imm(Lit(Int64.mul (Int64.of_int (List.length ctxt.layout)) 8L));Reg(Rsp)]);
      *)
      [(Movq, [Reg(Rbp); Reg(Rsp)]);
      (Popq, [Reg(Rbp)]);
      (Retq, []);
      ]
    | Br(lbl) -> [(Jmp, [Imm(Lbl(mk_lbl fn lbl))])]
    | Cbr(operand, lbl1, lbl2) -> 
      [compile_operand ctxt (Reg(Rax)) operand;
      (Cmpq, [(Imm(Lit(0L))); Reg(Rax)]);
      (J(Neq), [Imm(Lbl(mk_lbl fn lbl1))]);
      (Jmp, [Imm(Lbl(mk_lbl fn lbl2))])]
  end



(* compiling blocks --------------------------------------------------------- *)

(* We have left this helper function here for you to complete. 
   [fn] - the name of the function containing this block
   [ctxt] - the current context
   [blk]  - LLVM IR code for the block
*)
let compile_block (fn:string) (ctxt:ctxt) (blk:Ll.block) : ins list =
  (*compile the insns from block *)
  let rec compile_insns insns_list =
    begin match insns_list with
      | [] -> []
      | h::tl -> (compile_insn ctxt h)@(compile_insns tl)
    end
  in
  let compiled_insns = compile_insns blk.insns in

  (* compile terminator, concat behind compiled instructions*)
  let (_,term) = blk.term in
  let compiled_term = compile_terminator fn ctxt term in
  compiled_insns@compiled_term

let compile_lbl_block fn lbl ctxt blk : elem =
  Asm.text (mk_lbl fn lbl) (compile_block fn ctxt blk)


(* compile_fdecl ------------------------------------------------------------ *)


(* This helper function computes the location of the nth incoming
   function argument: either in a register or relative to %rbp,
   according to the calling conventions.  You might find it useful for
   compile_fdecl.

   [ NOTE: the first six arguments are numbered 0 .. 5 ]
*)
let arg_loc (n : int) : operand =
match n with
  | 0 -> Reg(Rdi)
  | 1 -> Reg(Rsi)
  | 2 -> Reg(Rdx)
  | 3 -> Reg(Rcx)
  | 4 -> Reg(R08)
  | 5 -> Reg(R09)
  (*the sixth element is the first which is directly on the stack
  start filling in stack from adress of old_rbp - 2*int64
  *)
  | _ -> Ind3(Lit(Int64.of_int ((-(n-6)-1)*8)), Rbp)
  

(* We suggest that you create a helper function that computes the
   stack layout for a given function declaration.

   - each function argument should be copied into a stack slot
   - in this (inefficient) compilation strategy, each local id
     is also stored as a stack slot.
   - see the discussion about locals
*)

(* creates mapping of all uids of a function: *)
(* highest stack address on top (at ret_addr)

ret_addr
old_rbp     <- rbp
arg_1
arg_2
arg_3
...
arg_n
uid_of_ins_1
uid_of_ins_2
uid_of_ins_3
...
uid_of_ins_n

*)

let stack_layout (args : uid list) ((start_block, lbled_blocks):cfg) : layout =

(* maps uids to stack slots; starts cur_ind above Rbp *)
let rec map_uids (args_to_map : uid list) (cur_ind:int) = 
  match args_to_map with
    | [] -> []
    | h::tl -> [(h, Ind3(Lit(Int64.of_int (cur_ind * -8)), Rbp))] @ (map_uids tl (cur_ind+1))
in
let arg_layout = map_uids args 1 in

(* extracts all uids from an insns list *)
let rec extract_insns_uids (insns : (uid * insn) list): uid list =
  match insns with
    | [] -> []
    | (cur_uid, cur_ins)::tl -> [cur_uid]@(extract_insns_uids tl)
in

(* exctracts all uids form a list of (label, block) tuples *)
let rec extract_uid_from_blocks (rem_blocks: (Ll.lbl * Ll.block) list): uid list =
    match rem_blocks with
      | [] -> []
      | (_,block)::tl -> (extract_insns_uids block.insns)@(extract_uid_from_blocks tl)
in
let uid_list_of_cfg = (extract_insns_uids start_block.insns)@extract_uid_from_blocks lbled_blocks in

(* concat layout from blocks behind layout from args, starting at index "arg_layout size" *)
arg_layout@(map_uids uid_list_of_cfg ((List.length arg_layout) + 1))


(* The code for the entry-point of a function must do several things:

   - since our simple compiler maps local %uids to stack slots,
     compiling the control-flow-graph body of an fdecl requires us to
     compute the layout (see the discussion of locals and layout)

   - the function code should also comply with the calling
     conventions, typically by moving arguments out of the parameter
     registers (or stack slots) into local storage space.  For our
     simple compilation strategy, that local storage space should be
     in the stack. (So the function parameters can also be accounted
     for in the layout.)

   - the function entry code should allocate the stack storage needed
     to hold all of the local stack slots.
*)
let compile_fdecl (tdecls:(tid * ty) list) (name:string) ({ f_ty; f_param; f_cfg }:fdecl) : prog =
let layout = stack_layout f_param f_cfg in
let rec map_params (param_list : Ll.uid list)ind =
  begin match param_list with
    | [] -> []
    | h::tl -> (map_params tl (ind + 1)) @ [(Movq, [(arg_loc ind);Reg(Rax)]);(Movq, [Reg(Rax);(lookup layout h)])]
  end
in

(* set rb to top uid (rsp += length of uid_layout * 8) *)
let save_old_rbp = [Pushq, [(Reg(Rbp))]] in

(* set rbp to value of rsp *)
let set_rbp = [Movq, [Reg(Rsp); Reg(Rbp)]] in

(* set rsp to top uid (rsp += length of uid_layout * 8) *)
let adjust_stackpointer = [(Subq, [Imm(Lit(Int64.mul (Int64.of_int (List.length layout)) 8L)); Reg(Rsp)])] in

(* set rsp to top uid (rsp += length of uid_layout * 8) *)
let move_args_to_stack = map_params f_param 0 in

(* extract last instruction from control flow graph *)
let (first_block, other_blocks) = f_cfg in

(* create context element for function *)
let ctxt = {tdecls = tdecls; layout = layout} in

(* compile the first block *)
let compiled_first_block = compile_block name ctxt first_block in

(* create first text element *)
let first_element =
[{lbl = name ; global = true ; asm = Text(
  save_old_rbp@
  set_rbp@
  adjust_stackpointer@
  move_args_to_stack@
  compiled_first_block)}]
in

(* creates a list of elemnts from labeld block lists *)
let rec compile_lbl_blocks (rem_blocks: (Ll.lbl * Ll.block) list): X86.elem list =
    match rem_blocks with
      | [] -> []
      | (lbl, curr_block)::tl -> [compile_lbl_block name lbl ctxt curr_block]@(compile_lbl_blocks tl)
in

(* compile all other elements *)
let other_elements = compile_lbl_blocks other_blocks in

first_element@other_elements



(* compile_gdecl ------------------------------------------------------------ *)
(* Compile a global value into an X86 global data declaration and map
   a global uid to its associated X86 label.
*)
let rec compile_ginit : ginit -> X86.data list = function
  | GNull     -> [Quad (Lit 0L)]
  | GGid gid  -> [Quad (Lbl (Platform.mangle gid))]
  | GInt c    -> [Quad (Lit c)]
  | GString s -> [Asciz s]
  | GArray gs | GStruct gs -> List.map compile_gdecl gs |> List.flatten
  | GBitcast (t1,g,t2) -> compile_ginit g

and compile_gdecl (_, g) = compile_ginit g


(* compile_prog ------------------------------------------------------------- *)
let compile_prog {tdecls; gdecls; fdecls} : X86.prog =
  let g = fun (lbl, gdecl) -> Asm.data (Platform.mangle lbl) (compile_gdecl gdecl) in
  let f = fun (name, fdecl) -> compile_fdecl tdecls name fdecl in
  (List.map g gdecls) @ (List.map f fdecls |> List.flatten)
