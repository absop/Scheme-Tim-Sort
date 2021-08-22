(parameterize ([compile-profile 'source])
  (load "tim-sort.v2.ss")
  (profile-dump-html))
