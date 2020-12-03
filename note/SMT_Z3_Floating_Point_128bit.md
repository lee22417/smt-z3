# 128bit Floating Point Add

### SMT LIB
- Terminal -> Command `z3 -smt2 -in`
- Code
```
(set-logic QF_FP)

(declare-const x (_ FloatingPoint 15 113))
(declare-const y (_ FloatingPoint 15 113))
(declare-const r (_ FloatingPoint 15 113))

(assert (and 
    (= x (fp #b0 #b011111111111111 #x0000000000000000000000000000))
    (= y (fp #b0 #b011111111111111 #x199999999999A000000000000000))
    (= r (fp.add roundTowardZero x y))
))

(check-sat)
(get-value (x y r))
```
-Result
```
sat
((x (fp #b0 #b011111111111111 #x0000000000000000000000000000))
 (y (fp #b0 #b011111111111111 #x199999999999a000000000000000))
 (r (fp #b0 #b100000000000000 #x0cccccccccccd000000000000000)))
```

### Z3 in F#
- Code
```Fsharp
let rec test_fp() =
    let ctx = new Ctx()    
    let rm = Native.Z3_mk_fpa_round_toward_zero(ctx.obj)
    
    let sort = Native.Z3_mk_fpa_sort_128(ctx.obj)    // 128 bit
    let sort2 = Native.Z3_mk_fpa_sort(ctx.obj,15u,64u) // 80 bit    
    
    // 128 bit
    let a3 = Native.Z3_mk_numeral(ctx.obj, "0", Native.Z3_mk_bv_sort(ctx.obj, 1u))
    let b3 = Native.Z3_mk_numeral(ctx.obj, "16383", Native.Z3_mk_bv_sort(ctx.obj, 15u))
    let c3 = Native.Z3_mk_numeral(ctx.obj, "0", Native.Z3_mk_bv_sort(ctx.obj, 112u))
    let x2 = Native.Z3_mk_fpa_fp(ctx.obj, a3, b3, c3)
    
    let a4 = Native.Z3_mk_numeral(ctx.obj, "0", Native.Z3_mk_bv_sort(ctx.obj, 1u))
    let b4 = Native.Z3_mk_numeral(ctx.obj, "16383", Native.Z3_mk_bv_sort(ctx.obj, 15u))
    let c4 = Native.Z3_mk_numeral(ctx.obj, "519229685853483224021651475660800", Native.Z3_mk_bv_sort(ctx.obj, 112u))
    let y2 = Native.Z3_mk_fpa_fp(ctx.obj, a4, b4, c4)
    
    let s_x_op_y = Native.Z3_mk_string_symbol(ctx.obj, "x_op_y");
    let x_op_y = Native.Z3_mk_const(ctx.obj, s_x_op_y, sort);
    let xy1 = Native.Z3_mk_eq(ctx.obj, x_op_y, Native.Z3_mk_fpa_add(ctx.obj, rm, x2, y2))
    
    let solver = Native.Z3_mk_solver(ctx.obj)
    let ass = Native.Z3_solver_assert(ctx.obj, solver, xy1)
    
    let check = Native.Z3_solver_check(ctx.obj, solver)
    let model = Native.Z3_solver_get_model(ctx.obj, solver)
    
    let getxy = Native.Z3_ast_to_string(ctx.obj, xy1)
    let getModel = Native.Z3_model_to_string(ctx.obj, model)
    
    printfn "xy1: %s\n %s" getxy getModel
    exit 0
```
- Result
```Fsharp
xy1: (= x_op_y
   (fp.add roundTowardZero
           (fp #b0 #b011111111111111 #x0000000000000000000000000000)
           (fp #b0 #b011111111111111 #x199999999999a000000000000000)))
 x_op_y -> (fp #b0 #b100000000000000 #x0cccccccccccd000000000000000)
```


# Reference
- SMT LIB
  - https://rise4fun.com/z3/tutorial 
  - https://stackoverflow.com/questions/15181211/qf-fpa-does-z3-support-ieee-754-arithmetic 
  - https://www.rapidtables.com/convert/number/hex-to-binary.html 
- Z3
  - https://github.com/Z3Prover/z3/blob/master/examples/c/test_capi.c 
  - https://z3prover.github.io/api/html/group__capi.html 
  - https://www.tutorialspoint.com/fsharp/fsharp_data_types.htm 
  
