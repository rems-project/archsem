Non-existing file
  $ archsem seq nonexistingfile.archsem.toml
  archsem: TESTS… arguments: no 'nonexistingfile.archsem.toml' file or
           directory
  Usage: archsem seq [OPTION]… TESTS…
  Try 'archsem seq --help' or 'archsem --help' for more information.
  [124]

Empty file
  $ archsem seq empty.archsem.toml
  archsem: fatal error: Failed to guess architecture in empty.archsem.toml with error :
          TOML field "arch" is missing
  [1]

Invalid architecture
  $ archsem seq invarch.archsem.toml
  archsem: fatal error: Failed to guess architecture in invarch.archsem.toml with error :
          Unknown architecture: "Nope"
  [1]

Invalid TOML
  $ archsem seq invtoml.archsem.toml
  archsem: fatal error: Failed to guess architecture in invtoml.archsem.toml with error :
          TOML parse error at line 2, character 10: line breaks are not allowed inside strings
  [1]

Just architecture and nothing else
  $ archsem seq justarch.archsem.toml
  archsem: internal error, uncaught exception:
           TOML field "memory" is missing
           
  
  arm-seq  1 test(s)
  
  [125]

Missing "step" in memory field
  $ archsem seq missing-step.archsem.toml
  archsem: internal error, uncaught exception:
           TOML field "step" is missing at memory.[0]
           
  
  arm-seq  1 test(s)
  
  [125]

Invalid "step" in memory field
  $ archsem seq invalid-step.archsem.toml
  archsem: internal error, uncaught exception:
           TOML error at "memory.[0].step": Expected integer, found string
           
  
  arm-seq  1 test(s)
  
  [125]

Too much data for step
  $ archsem seq too-much-data.archsem.toml
  archsem: internal error, uncaught exception:
           TOML error at "memory.[0].data": Memory data number (0xca020020) contains 4 bytes but the step is 2
           
  
  arm-seq  1 test(s)
  
  [125]

Invalid reset value in Isla file
  $ archsem convert --format isla invalid-reset.litmus.toml
  archsem: internal error, uncaught exception:
           TOML error at "thread.reset.X0": register X0 has invalid reset value: Isla value is invalid, should be int or string, but is: true
           
  [125]
