let main (n: i32): *[]i32 =
  let xs = iota(n)
  let xs[1] = xs[0]
  let ys =
    if xs[0] > 0 then
      xs
    else
      indices xs

  let ys[2] = 4
  in ys
