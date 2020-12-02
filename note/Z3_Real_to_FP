# Real to Floating Point Conversion

### Z3 , Fsharp
- Code
```Fsharp
let test_fp2() =
    let ctx = new Ctx()    
    let rm = Native.Z3_mk_fpa_round_toward_zero(ctx.obj)
    
    let sort = Native.Z3_mk_fpa_sort_128(ctx.obj)    // 128 bit
    let sort2 = Native.Z3_mk_fpa_sort(ctx.obj,15u,65u) // 80 bit    
    
    // 128 bit
    // real to fp
    let xReal = Native.Z3_mk_real(ctx.obj, 1, 1)
    let xx1 = Native.Z3_mk_fpa_to_fp_real(ctx.obj, rm, xReal, sort)
    let yReal = Native.Z3_mk_real(ctx.obj, 11, 10)
    let yy1 = Native.Z3_mk_fpa_to_fp_real(ctx.obj, rm, yReal, sort)
    
    let s_x_op_y = Native.Z3_mk_string_symbol(ctx.obj, "x_op_y");
    let x_op_y = Native.Z3_mk_const(ctx.obj, s_x_op_y, sort);
    let xy1 = Native.Z3_mk_eq(ctx.obj, x_op_y, Native.Z3_mk_fpa_div(ctx.obj, rm, xx1, yy1))
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
-Result
```
xy1: (= x_op_y
   (fp.div roundTowardZero
           ((_ to_fp 15 113) roundTowardZero 1.0)
           ((_ to_fp 15 113) roundTowardZero (/ 11.0 10.0))))
 x_op_y -> (fp #b0 #b011111111111110 #xd1745d1745d1745d1745d1745d18)
```


# Reference
- https://z3prover.github.io/api/html/group__capi.html#ga10f219c61da2e7371e8443d8a19beacb
