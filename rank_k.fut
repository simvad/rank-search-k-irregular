import "lib/github.com/diku-dk/cpprandom/random"
module rng_engine = minstd_rand
module rand_i64 = uniform_int_distribution i64 rng_engine

let scanExc 't [n] (op: t->t->t) (ne: t) (arr : [n]t) : [n]t =
    scan op ne <| map (\i -> if i>0 then arr[i-1] else ne) (iota n)

let mkFlagArray 't [m]
            (aoa_shp: [m]i64) (zero: t)       
            (aoa_val: [m]t  ) : []t =         
  let shp_rot = map (\i->if i==0 then 0      
                         else aoa_shp[i-1]
                    ) (iota m)
  let shp_scn = scan (+) 0 shp_rot            
  let aoa_len = shp_scn[m-1]+aoa_shp[m-1]     
  let shp_ind = map2 (\shp ind ->            
                       if shp==0 then -1      
                       else ind               
                     ) aoa_shp shp_scn        
  in scatter (replicate aoa_len zero)        
             shp_ind aoa_val                  
                                              
let sgmscan 't [n] (op: t->t->t) (ne: t) (flg : [n]i64) (arr : [n]t) : [n]t =
  let flgs_vals =
    scan ( \ (f1, x1) (f2,x2) ->
            let f = f1 | f2 in
            if f2 != 0 then (f, x2)
            else (f, op x1 x2) )
         (0,ne) (zip flg arr)
  let (_, vals) = unzip flgs_vals
  in vals

let expand [n] (s:[]i64) (f: [n]i64) (arr: []i64) : [n]i64 =
    let arr_flags = mkFlagArray s 0 arr :> [n]i64
    in sgmscan (+) 0 f arr_flags

let pivotGenerator [m] (rng:rng_engine.rng) (s: [m]i64) =
    let rngs = rng_engine.split_rng m rng :> [m]rng_engine.rng
    let tmp = unzip (map2 (\r s->rand_i64.rand(0,s) r) rngs s)
    let rngs = tmp.0
    let vals = tmp.1
    let rng = rng_engine.join_rng rngs
    in (rng, vals)

let split [n][m] (d_as:[n]i64) (s_as:[m]i64) (rng:rng_engine.rng): ([n]i64,[3][n]i64, [m][3]i64, rng_engine.rng) =
    let f_as = mkFlagArray s_as 0 (replicate m 1i64) :> [n]i64
    let tmp = pivotGenerator rng s_as
    let rng = tmp.0
    let ps = tmp.1 
    let p_exp = expand s_as f_as ps 
    let b_as = scanExc (+) 0 s_as
    let b_exp = expand s_as f_as b_as
    let c = map3 (\d p b -> if d<d_as[p+b-1] then 0 else if d==d_as[p+b-1] then 1 else 2) d_as p_exp b_exp:> [n]i64
    let cs = tabulate_2d 3 n (\i j -> if c[j] == i then 1 else 0) :> [3][n]i64
    let cs_cumm= (map (sgmscan (+) 0 f_as) cls)
    let is = scatter (replicate n (-1)) (map (\x->x-1)(map2 (+) b_as s_as)) ((0...m-1):>[m]i64) :>[n]i64
    let splits = transpose(map (scatter (replicate m 0) is) cs_cumm):> [m][3]i64
    in (f_as,cs,splits,rng)

let merge [n] [m] (d_as:[n]i64) (s_as: [m]i64) (all:[3][n]i64) (cls:[3][n]i64) =
    let remains = map (i64.sum) (transpose (map2 (map2 (\a c-> a*c)) all cls))
    let remains_count = reduce (+) 0 remains
    let is = map (\x->x-1) (map2 (\r rs->r*rs) remains (scan (+) 0 remains))
    let d_res = scatter (replicate remains_count 0) is d_as
    let s_res = 
    in (s_res,d_res)

let rank_k [l] (s_as: [l]i64) (d_as: []i64) (ks: [l]i64): [l]i64 =
    let rng = rng_engine.rng_from_seed [123]
    let stop = (reduce (+) 0 s_as) <= length s_as
    let d_res = replicate l 0
    let (_, d_res,_,_,_,_) =
        loop (s_as, d_as,rng,ks, stop) while (!stop) do
            let tmp_split = split d_as s_as rng
            let f_as = tmp_split.0
            let cls = tmp_split.1
            let splits = tmp_split.2  
            let rng = tmp_split.3
            let lth = (map (\x->i64.bool x) (map (\i-> ks[i]<=splits[i][0]) (iota l))) :>[l]i64
            let eq = map (\x->i64.bool x) (map (\i->(ks[i]>splits[i][0]) && ((ks[i]<=(i64.sum splits[i][:2])))) (iota l)) :>[l]i64
            let gth = map (\x->i64.bool x) (map (\i->ks[i]>(i64.sum splits[i][:2])) (iota l)) :>[l]i64
            let all = map (expand s_as f_as) [lth,eq,gth]
            let ks_new = (map (\i -> if splits[i][2]==1 then ks[i]-(i64.sum splits[i][:2]) else ks[i]) (iota l)) 
            let tmp_merge = merge d_as s_as all cls
            let s_res = tmp_merge.0
            let d_res = tmp_merge.1
            in (s_res, d_res,ks_new, rng, (reduce (+) 0 s_res)<=(length s_res) )
    in d_res     
            