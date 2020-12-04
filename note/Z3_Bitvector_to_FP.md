# Real to Floating Point Conversion

### Z3 , Fsharp
- Bitvector to 80bit floating point / 128bit floating point
- Code
```Fsharp
let test_fp() =
    let ctx = new Ctx()    
    let rm = Native.Z3_mk_fpa_round_toward_zero(ctx.obj)
    
    let sort = Native.Z3_mk_fpa_sort_128(ctx.obj)    // 128 bit
    let sort2 = Native.Z3_mk_fpa_sort(ctx.obj,15u,64u) // 80 bit    
    
    // Bitvec to 80 bit
    // 80bit in C -> 79bit 
    let xbv1 = Native.Z3_mk_numeral(ctx.obj, "151106504079791792062464", Native.Z3_mk_bv_sort(ctx.obj, 79u))
    let ybv1 = Native.Z3_mk_numeral(ctx.obj, "151107426416995477540864", Native.Z3_mk_bv_sort(ctx.obj, 79u))
    let x1 = Native.Z3_mk_fpa_to_fp_bv(ctx.obj, xbv1, sort2)
    let y1 = Native.Z3_mk_fpa_to_fp_bv(ctx.obj, ybv1, sort2)
    
    // Bitvec to 128 bit
    let xbv2 = Native.Z3_mk_numeral(ctx.obj, "85065399433376081038215121361612832768", Native.Z3_mk_bv_sort(ctx.obj, 128u))
    let ybv2 = Native.Z3_mk_numeral(ctx.obj, "85065918663061934521439143013088493568", Native.Z3_mk_bv_sort(ctx.obj, 128u))
    let x2 = Native.Z3_mk_fpa_to_fp_bv(ctx.obj, xbv2, sort)
    let y2 = Native.Z3_mk_fpa_to_fp_bv(ctx.obj, ybv2, sort)
    
    let s_x_op_y = Native.Z3_mk_string_symbol(ctx.obj, "x_op_y");
    let x_op_y = Native.Z3_mk_const(ctx.obj, s_x_op_y, sort);
    let xy1 = Native.Z3_mk_eq(ctx.obj, x_op_y, Native.Z3_mk_fpa_add(ctx.obj, rm, x2, y2))
//    let xy2 = Native.Z3_mk_eq(ctx.obj, x_op_y, x2)
    
    let solver = Native.Z3_mk_solver(ctx.obj)
    let ass = Native.Z3_solver_assert(ctx.obj, solver, xy1)
    
    let check = Native.Z3_solver_check(ctx.obj, solver)
    let model = Native.Z3_solver_get_model(ctx.obj, solver)
    
    let getxy = Native.Z3_ast_to_string(ctx.obj, xy1)
    let getModel = Native.Z3_model_to_string(ctx.obj, model)
    
    printfn "xy1: %s\n %s" getxy getModel
    exit 0
```
- Result (128bit case)
```
xy1: (= x_op_y
   (fp.add roundTowardZero
           ((_ to_fp 15 113) #x3fff0000000000000000000000000000)
           ((_ to_fp 15 113) #x3fff199999999999a000000000000000)))
 x_op_y -> (fp #b0 #b100000000000000 #x0cccccccccccd000000000000000)
```


# Reference
- https://z3prover.github.io/api/html/group__capi.html#ga10f219c61da2e7371e8443d8a19beacb
