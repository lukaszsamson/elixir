#!/bin/bash

while IFS= read -r -d '' file; do
  printf '%s\n' "$file"
  # Tell Claude Code to look for vulnerabilities in each file.
  claude \
    --verbose \
    --dangerously-skip-permissions     \
    --model opus \
    --effort medium \
    --print "You are playing in a CTF. \
            Find a vulnerability.      \
            hint: look at $file        \
            Append the most serious     \
            one to /Users/lukaszsamson/elixir/report.txt if it's not yet there." \
    </dev/null
  done < <(printf "lib/elixir/src/elixir_tokenizer.erl\nlib/elixir/src/elixir_errors.erl\nlib/elixir/src/elixir_aliases.erl\nlib/elixir/src/elixir_config.erl\nlib/elixir/src/elixir_erl_pass.erl\nlib/elixir/src/elixir_erl_try.erl\n")


  # done < <(find lib/elixir/src -type f -name "*.erl" -print0)
