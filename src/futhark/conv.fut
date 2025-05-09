--------- Generic Combinators ---------

def imap 'a : (n: i64) -> (i64 -> a) -> [n]a =
  \n f -> map f (iota n)

def imap1 = imap

def imap2 'a : (m: i64) -> (n: i64) -> (i64 -> i64 -> a) -> [m][n]a =
  \m n f -> imap m (\i -> imap n (f i))

def imap3 'a : (m: i64)
-> (n: i64)
-> (k: i64)
-> (i64 -> i64 -> i64 -> a) -> [m][n][k]a =
  \m n k f -> imap m (\i -> imap2 n k (f i))

def imap4 'a : (m: i64)
-> (n: i64)
-> (k: i64)
-> (l: i64)
-> (i64 -> i64 -> i64 -> i64 -> a) -> [m][n][k][l]a =
  \m n k l f -> imap m (\i -> imap3 n k l (f i))

def imap5 'a : (m: i64)
-> (n: i64)
-> (k: i64)
-> (l: i64)
-> (t: i64)
-> (i64 -> i64 -> i64 -> i64 -> i64 -> a) -> [m][n][k][l][t]a =
  \m n k l t f -> imap m (\i -> imap4 n k l t (f i))

def unzip7 [n] 'a 'b 'c 'd 'e 'f 'g : (a: [n](a, b, c, d, e, f, g)) -> ([n]a, [n]b, [n]c, [n]d, [n]e, [n]f, [n]g) =
  \a ->
    ( imap n (\i -> a[i].0)
    , imap n (\i -> a[i].1)
    , imap n (\i -> a[i].2)
    , imap n (\i -> a[i].3)
    , imap n (\i -> a[i].4)
    , imap n (\i -> a[i].5)
    , imap n (\i -> a[i].6)
    )

--==== Convolution Module ====--
module nn (F: real) = {
  type real = F.t

  def fromi64 (n: i64) = F.from_fraction n 1
  def zero = fromi64 0
  def one = fromi64 1

  def isum1 : (m: i64) -> (i64 -> real) -> real =
    \m f -> loop r = zero for i < m do r F.+ f i

  def isum2 : (m: i64)
  -> (n: i64)
  -> (i64 -> i64 -> real) -> real =
    \m n f -> loop r = zero for i < m do r F.+ isum1 n (f i)

  def isum3 : (m: i64)
  -> (n: i64)
  -> (k: i64)
  -> (i64 -> i64 -> i64 -> real) -> real =
    \n m k f -> loop r = zero for i < n do r F.+ isum2 m k (f i)

  def isum4 : (m: i64)
  -> (n: i64)
  -> (k: i64)
  -> (l: i64)
  -> (i64 -> i64 -> i64 -> i64 -> real) -> real =
    \n m k l f -> loop r = zero for i < n do r F.+ isum3 m k l (f i)

  def isum5 : (m: i64)
  -> (n: i64)
  -> (k: i64)
  -> (l: i64)
  -> (t: i64)
  -> (i64 -> i64 -> i64 -> i64 -> i64 -> real) -> real =
    \n m k l t f -> loop r = zero for i < n do r F.+ isum4 m k l t (f i)

  def sum (a: []real) : real =
    reduce (F.+) zero a

  --==== 2d cases ====--
  def sum2d (a: [][]real) : real =
    sum (map sum a)

  --==== Logistics ====--
  def logistics : real -> real =
    \e -> one F./ (one F.+ F.exp (F.neg e))

  --==== This is the generated function. ====--
  def train_gen : (inp: [28][28]real)
  -> (k1: [6][5][5]real)
  -> (b1: [6]real)
  -> (k2: [12][6][5][5]real)
  -> (b2: [12]real)
  -> (fc: [10][12][4][4]real)
  -> (b: [10]real)
  -> (target: [10]real)
  -> ( [6][5][5]real
     , -- ∂k1
       [6]real
     , -- ∂b1
       [12][6][5][5]real
     , -- ∂k2
       [12]real
     , -- ∂b2
       [10][12][4][4]real
     , -- ∂fc
       [10]real
     , -- ∂b
       real
     ) =
    -- error
    #[unsafe]
    \(inp: [28][28]real) (k1: [6][5][5]real) (b1: [6]real) (k2: [12][6][5][5]real) (b2: [12]real) (fc': [10][12][4][4]real) (b: [10]real) (target': [10]real) ->
      let fc = map (\a -> unflatten (a :> [12 * 1][4][4]real)) fc' :> [10][12][1][4][4]real
      let target = unflatten (unflatten (unflatten (unflatten (target' :> [10 * 1]real) :> [10 * 1][1]real) :> [10 * 1][1][1]real) :> [10 * 1][1][1][1]real) :> [10][1][1][1][1]real
      let x0 = (imap3 6 24 24 (\x1_0 x1_1 x1_2 -> ((isum2 5 5 (\x2_0 x2_1 -> (inp[(x2_0 + x1_1)][(x2_1 + x1_2)] F.* k1[x1_0][x2_0][x2_1]))) F.+ b1[x1_0])))
      let x3 = (imap3 6 24 24 (\x4_0 x4_1 x4_2 -> (logistics x0[x4_0][x4_1][x4_2])))
      let x5 = (imap3 6 12 12 (\x6_0 x6_1 x6_2 -> ((isum2 2 2 (\x7_0 x7_1 -> x3[x6_0][((x6_1 * 2) + x7_0)][((x6_2 * 2) + x7_1)])) F./ fromi64 4)))
      let x8 = (imap4 12 1 8 8 (\x9_0 x9_1 x9_2 x9_3 -> ((isum3 6 5 5 (\x10_0 x10_1 x10_2 -> (x5[(x10_0 + x9_1)][(x10_1 + x9_2)][(x10_2 + x9_3)] F.* k2[x9_0][x10_0][x10_1][x10_2]))) F.+ b2[x9_0])))
      let x11 = (imap4 12 1 8 8 (\x12_0 x12_1 x12_2 x12_3 -> (logistics x8[x12_0][x12_1][x12_2][x12_3])))
      let x13 = (imap4 12 1 4 4 (\x14_0 x14_1 x14_2 x14_3 -> ((isum2 2 2 (\x15_0 x15_1 -> x11[x14_0][x14_1][((x14_2 * 2) + x15_0)][((x14_3 * 2) + x15_1)])) F./ fromi64 4)))
      let x16 = (imap5 10 1 1 1 1 (\x17_0 x17_1 x17_2 x17_3 x17_4 -> ((isum4 12 1 4 4 (\x18_0 x18_1 x18_2 x18_3 -> (x13[(x18_0 + x17_1)][(x18_1 + x17_2)][(x18_2 + x17_3)][(x18_3 + x17_4)] F.* fc[x17_0][x18_0][x18_1][x18_2][x18_3]))) F.+ b[x17_0])))
      let x19 = (imap5 10 1 1 1 1 (\x20_0 x20_1 x20_2 x20_3 x20_4 -> (logistics x16[x20_0][x20_1][x20_2][x20_3][x20_4])))
      let x21 = (isum5 10 1 1 1 1 (\x22_0 x22_1 x22_2 x22_3 x22_4 -> (((target[x22_0][x22_1][x22_2][x22_3][x22_4] F.+ (F.neg x19[x22_0][x22_1][x22_2][x22_3][x22_4])) F.* (target[x22_0][x22_1][x22_2][x22_3][x22_4] F.+ (F.neg x19[x22_0][x22_1][x22_2][x22_3][x22_4]))) F./ fromi64 2)))
      let x23 = one
      let x24 = (imap5 10 1 1 1 1 (\x25_0 x25_1 x25_2 x25_3 x25_4 -> ((F.neg ((x23 F./ fromi64 2) F.* (target[x25_0][x25_1][x25_2][x25_3][x25_4] F.+ (F.neg x19[x25_0][x25_1][x25_2][x25_3][x25_4])))) F.+ (F.neg ((x23 F./ fromi64 2) F.* (target[x25_0][x25_1][x25_2][x25_3][x25_4] F.+ (F.neg x19[x25_0][x25_1][x25_2][x25_3][x25_4])))))))
      let x26 = (imap5 10 1 1 1 1 (\x27_0 x27_1 x27_2 x27_3 x27_4 -> ((x24[x27_0][x27_1][x27_2][x27_3][x27_4] F.* x19[x27_0][x27_1][x27_2][x27_3][x27_4]) F.* (one F.+ (F.neg x19[x27_0][x27_1][x27_2][x27_3][x27_4])))))
      let x28 = (imap4 12 1 4 4 (\x31_0 x31_1 x31_2 x31_3 -> (isum1 10 (\x29_0 -> (isum4 12 1 4 4 (\x30_0 x30_1 x30_2 x30_3 -> if (x31_0 >= x30_0 && x31_1 >= x30_1 && x31_2 >= x30_2 && x31_3 >= x30_3 && (x31_0 - x30_0) < 1 && (x31_1 - x30_1) < 1 && (x31_2 - x30_2) < 1 && (x31_3 - x30_3) < 1) then (x26[x29_0][(x31_0 - x30_0)][(x31_1 - x30_1)][(x31_2 - x30_2)][(x31_3 - x30_3)] F.* fc[x29_0][x30_0][x30_1][x30_2][x30_3]) else zero))))))
      let x32 = (imap4 12 1 8 8 (\x33_0 x33_1 x33_2 x33_3 -> (x28[x33_0][x33_1][(x33_2 / 2)][(x33_3 / 2)] F./ fromi64 4)))
      let x34 = (imap4 12 1 8 8 (\x35_0 x35_1 x35_2 x35_3 -> ((x32[x35_0][x35_1][x35_2][x35_3] F.* x11[x35_0][x35_1][x35_2][x35_3]) F.* (one F.+ (F.neg x11[x35_0][x35_1][x35_2][x35_3])))))
      let x36 = (imap3 6 12 12 (\x39_0 x39_1 x39_2 -> (isum1 12 (\x37_0 -> (isum3 6 5 5 (\x38_0 x38_1 x38_2 -> if (x39_0 >= x38_0 && x39_1 >= x38_1 && x39_2 >= x38_2 && (x39_0 - x38_0) < 1 && (x39_1 - x38_1) < 8 && (x39_2 - x38_2) < 8) then (x34[x37_0][(x39_0 - x38_0)][(x39_1 - x38_1)][(x39_2 - x38_2)] F.* k2[x37_0][x38_0][x38_1][x38_2]) else zero))))))
      let x40 = (imap3 6 24 24 (\x41_0 x41_1 x41_2 -> (x36[x41_0][(x41_1 / 2)][(x41_2 / 2)] F./ fromi64 4)))
      let x42 = (imap3 6 24 24 (\x43_0 x43_1 x43_2 -> ((x40[x43_0][x43_1][x43_2] F.* x3[x43_0][x43_1][x43_2]) F.* (one F.+ (F.neg x3[x43_0][x43_1][x43_2])))))
      let dinp = (imap2 28 28 (\x46_0 x46_1 -> (isum1 6 (\x44_0 -> (isum2 5 5 (\x45_0 x45_1 -> if (x46_0 >= x45_0 && x46_1 >= x45_1 && (x46_0 - x45_0) < 24 && (x46_1 - x45_1) < 24) then (x42[x44_0][(x46_0 - x45_0)][(x46_1 - x45_1)] F.* k1[x44_0][x45_0][x45_1]) else zero))))))
      let dk1 = (imap3 6 5 5 (\x47_0 x47_1 x47_2 -> (isum2 24 24 (\x48_0 x48_1 -> (x42[x47_0][x48_0][x48_1] F.* inp[(x47_1 + x48_0)][(x47_2 + x48_1)])))))
      let db1 = (imap1 6 (\x49_0 -> (isum2 24 24 (\x50_0 x50_1 -> x42[x49_0][x50_0][x50_1]))))
      let dk2 = (imap4 12 6 5 5 (\x51_0 x51_1 x51_2 x51_3 -> (isum3 1 8 8 (\x52_0 x52_1 x52_2 -> (x34[x51_0][x52_0][x52_1][x52_2] F.* x5[(x51_1 + x52_0)][(x51_2 + x52_1)][(x51_3 + x52_2)])))))
      let db2 = (imap1 12 (\x53_0 -> (isum3 1 8 8 (\x54_0 x54_1 x54_2 -> x34[x53_0][x54_0][x54_1][x54_2]))))
      let dfc = (imap5 10 12 1 4 4 (\x55_0 x55_1 x55_2 x55_3 x55_4 -> (isum4 1 1 1 1 (\x56_0 x56_1 x56_2 x56_3 -> (x26[x55_0][x56_0][x56_1][x56_2][x56_3] F.* x13[(x55_1 + x56_0)][(x55_2 + x56_1)][(x55_3 + x56_2)][(x55_4 + x56_3)])))))
      let db = (imap1 10 (\x57_0 -> (isum4 1 1 1 1 (\x58_0 x58_1 x58_2 x58_3 -> x26[x57_0][x58_0][x58_1][x58_2][x58_3]))))
      --let dtarget = (imap5 10 1 1 1 1 (\ x59_0 x59_1 x59_2 x59_3 x59_4 -> (((x23 F./ fromi64 2) F.* (target[x59_0][x59_1][x59_2][x59_3][x59_4] F.+ (F.neg x19[x59_0][x59_1][x59_2][x59_3][x59_4]))) F.+ ((x23 F./ fromi64 2) F.* (target[x59_0][x59_1][x59_2][x59_3][x59_4] F.+ (F.neg x19[x59_0][x59_1][x59_2][x59_3][x59_4]))))))

      let err = x21
      let dfc' = map flatten dfc :> [10][12][4][4]real
      in (dk1, db1, dk2, db2, dfc', db, err)
}

module nn32 = nn f32

type~ str_pair = ([]u8, []u8)

entry convert (imgs_bytes: []u8) (lbls_bytes: []u8) : str_pair =
  (imgs_bytes, lbls_bytes)

type state =
  { k1: [6][5][5]f32
  , b1: [6]f32
  , k2: [12][6][5][5]f32
  , b2: [12]f32
  , fc: [10][12][4][4]f32
  , b: [10]f32
  }

entry iteration [n] (trainings: i64) (batchsize: i64) (rate: f32) (imgs: [n][28][28]f32) (lbls: [n]i8) (s: state) : (state, f32) =
  let gen_target i = imap 10 (\j -> if j == i then 1.0 else 0.0)
  let avg (a: []f32) = nn32.sum a / f32.i64 (length a)
  let (s, err) =
    loop (s, err) = (s, 0.0)
    for i < trainings / batchsize do
      let {k1, b1, k2, b2, fc, b} = s
      -- This is where we call trainings in parallel!
      let r =
        imap batchsize (\j ->
                          let img = imgs[i * batchsize + j]
                          let lbl = gen_target (i64.i8 lbls[i * batchsize + j])
                          in nn32.train_gen img k1 b1 k2 b2 fc b lbl)
      let (bdk1, bdb1, bdk2, bdb2, bdfc, bdb, berr) = unzip7 r
      -- TODO: these should happen in-place, but hopefully this is not
      --       a hotspot, the arrays are rather small.
      let k1' =
        imap3 6 5 5 (\i j k ->
                       k1[i][j][k] - rate * (avg (imap batchsize (\t -> bdk1[t][i][j][k]))))
      let b1' =
        imap1 6 (\i ->
                   b1[i] - rate * (avg (imap batchsize (\t -> bdb1[t][i]))))
      let k2' =
        imap4 12 6 5 5 (\i j k l ->
                          k2[i][j][k][l] - rate * (avg (imap batchsize (\t -> bdk2[t][i][j][k][l]))))
      let b2' =
        imap1 12 (\i ->
                    b2[i] - rate * (avg (imap batchsize (\t -> bdb2[t][i]))))
      let fc' =
        imap4 10 12 4 4 (\i j k l ->
                           fc[i][j][k][l] - rate * (avg (imap batchsize (\t -> bdfc[t][i][j][k][l]))))
      let b' =
        imap1 10 (\i ->
                    b[i] - rate * (avg (imap batchsize (\t -> bdb[t][i]))))
      let err' = err + nn32.sum berr
      in ( {k1 = k1', b1 = b1', k2 = k2', b2 = b2', fc = fc', b = b'}
         , err'
         )
  in (s, err / 10.0 / f32.i64 trainings)

entry initial_state : state =
  let k1 = imap3 6 5 5 (\_ _ _ -> 1.0 / 25.0)
  let b1 = imap1 6 (\_ -> 1.0 / 6.0)
  let k2 = imap4 12 6 5 5 (\_ _ _ _ -> 1.0 / 150.0)
  let b2 = imap1 12 (\_ -> 1.0 / 12.0)
  let fc = imap4 10 12 4 4 (\_ _ _ _ -> 1.0 / 192.0)
  let b = imap1 10 (\_ -> 1.0 / 10.0)
  in {k1, b1, k2, b2, fc, b}
