Non-existing file
  $ archsem seq nonexistingfile.archsem.toml
  archsem: TESTS… arguments: no 'nonexistingfile.archsem.toml' file or
           directory
  Usage: archsem seq [--config=FILE] [--format=FMT] [OPTION]… TESTS…
  Try 'archsem seq --help' or 'archsem --help' for more information.
  [124]

Empty file
  $ archsem seq empty.archsem.toml
  archsem: fatal error: Failed to guess architecture in empty.archsem.toml with error :
          Otoml__Common.Key_error("Failed to retrieve a value at arch: field arch not found")
  [1]

Invalid architecture
  $ archsem seq invarch.archsem.toml
  archsem: fatal error: Failed to guess architecture in invarch.archsem.toml with error :
          Unknown architecture: "Nope"
  [1]
