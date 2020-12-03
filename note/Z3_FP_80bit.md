# 80bit Floating Point Div
- 80bit FP in C is the same range and precision as 79bit FP in Z3

### Z3 in F#
- Code
```Fsharp
let rec test_fp() =
    let ctx = new Ctx()    
    let rm = Native.Z3_mk_fpa_round_toward_zero(ctx.obj)
    
    let sort = Native.Z3_mk_fpa_sort_128(ctx.obj)    // 128 bit
    let sort2 = Native.Z3_mk_fpa_sort(ctx.obj,15u,64u) // 80 bit FP in C
    
    // 80 bit
    let a1 = Native.Z3_mk_numeral(ctx.obj, "0", Native.Z3_mk_bv_sort(ctx.obj, 1u))
    let b1 = Native.Z3_mk_numeral(ctx.obj, "16383", Native.Z3_mk_bv_sort(ctx.obj, 15u))
    // fraction part = m - 9223372036854775808 
    let c1 = Native.Z3_mk_numeral(ctx.obj, "0", Native.Z3_mk_bv_sort(ctx.obj, 63u))
    let x1 = Native.Z3_mk_fpa_fp(ctx.obj, a1, b1, c1)
    
    let a2 = Native.Z3_mk_numeral(ctx.obj, "0", Native.Z3_mk_bv_sort(ctx.obj, 1u))
    let b2 = Native.Z3_mk_numeral(ctx.obj, "16383", Native.Z3_mk_bv_sort(ctx.obj, 15u))
    let c2 = Native.Z3_mk_numeral(ctx.obj, "922337203685478400", Native.Z3_mk_bv_sort(ctx.obj, 63u))
    let y1 = Native.Z3_mk_fpa_fp(ctx.obj, a2, b2, c2)
    
    let s_x_op_y = Native.Z3_mk_string_symbol(ctx.obj, "x_op_y");
    let x_op_y = Native.Z3_mk_const(ctx.obj, s_x_op_y, sort2);
    let xy1 = Native.Z3_mk_eq(ctx.obj, x_op_y, Native.Z3_mk_fpa_div(ctx.obj, rm, x1, y1))
//    let xy2 = Native.Z3_mk_eq(ctx.obj, x_op_y, xx1)
    
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
   (fp.div roundTowardZero
           (fp #b0
               #b011111111111111
               #b000000000000000000000000000000000000000000000000000000000000000)
           (fp #b0
               #b011111111111111
               #b000110011001100110011001100110011001100110011001101000000000000)))
 x_op_y -> (fp #b0 #b011111111111110 #b110100010111010001011101000101110100010111010001011010011100100)
```
