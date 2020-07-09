-- type vec = (f32, f32, f32, f32)

-- let vecadd (a: vec) (b: vec) =
--   (a.0 + b.0, a.1 + b.1, a.2 + b.2, a.3 + b.3)

-- let psum = scan vecadd (0,0,0,0)

let psum = scan (+) 0

let main (xss: [][]i32) =
  #[incremental_flattening(only_intra)]
  map (psum >-> psum >-> psum)
      xss
