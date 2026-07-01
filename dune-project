(lang dune 2.0)

(name lambda-S-dti)
(version 0.1)

(using menhir 2.0)
(generate_opam_files true)

(source (github SoftwareFoundationGroupAtKyotoU/lambda-S-dti))

(package
 (name lambda-S-dti)
 
 (synopsis "Interpreter and compiler of the ITGL with dynamic type inference using space-efficient coercions")
 (authors
  "Yusuke Miyazaki <miyazaki@fos.kuis.kyoto-u.ac.jp>"
  "Yuki Oshima <y.oshima@fos.kuis.kyoto-u.ac.jp>"
  )
 (maintainers "y.oshima@fos.kuis.kyoto-u.ac.jp")
 (license "MIT")
 
 (depends
  (ocaml (>= 4.14.1))
  (dune (>= 2.0))
  
  (menhir (>= 2.0))
  (core (>= v0.17))
  (core_bench (>= v0.17))
  (core_unix (>= v0.17))
  (yojson (>= 2.0))
  
  (llvm (>="19-static"))
  (ounit2 (and :with-test (>= 2.0)))
 )
)
