let main (n: i32): i32 =
  let xs = iota 10
  let x = reduce (+) n xs
  let ys = iota 10
  let y = reduce (+) (x*n) ys
  in x + y
