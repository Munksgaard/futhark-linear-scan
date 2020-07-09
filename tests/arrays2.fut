let main (n: i32): i32=
  let xs = iota(10)
  let xs[1] = xs[0]

  let x = reduce (+) 0 xs

  let ys = iota(10)
  let ys[1] = ys[0]

  let y = reduce (+) 0 (scan (+) 0 ys)

  in x + y
